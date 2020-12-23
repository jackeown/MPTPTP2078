%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JDNuNpv1XY

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:29 EST 2020

% Result     : Theorem 53.04s
% Output     : Refutation 53.04s
% Verified   : 
% Statistics : Number of formulae       :  181 (1755 expanded)
%              Number of leaves         :   24 ( 539 expanded)
%              Depth                    :   31
%              Number of atoms          : 1638 (16546 expanded)
%              Number of equality atoms :  101 (1118 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X34: $i,X38: $i] :
      ( ( X38
        = ( k1_tarski @ X34 ) )
      | ( ( sk_C_1 @ X38 @ X34 )
        = X34 )
      | ( r2_hidden @ ( sk_C_1 @ X38 @ X34 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ( X37 = X34 )
      | ( X36
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X34: $i,X37: $i] :
      ( ( X37 = X34 )
      | ~ ( r2_hidden @ X37 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X1 )
      | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X35 != X34 )
      | ( r2_hidden @ X35 @ X36 )
      | ( X36
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X34: $i] :
      ( r2_hidden @ X34 @ ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('31',plain,(
    ! [X34: $i] :
      ( r2_hidden @ X34 @ ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['24'])).

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

thf('32',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X34: $i,X37: $i] :
      ( ( X37 = X34 )
      | ~ ( r2_hidden @ X37 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X34: $i,X37: $i] :
      ( ( X37 = X34 )
      | ~ ( r2_hidden @ X37 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('56',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('60',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','63'])).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('73',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('82',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('86',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('94',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X3
        = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['83','99'])).

thf('101',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('102',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('107',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('108',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('110',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ k1_xboole_0 ) @ X3 ) ) ),
    inference(demod,[status(thm)],['100','105','108','109'])).

thf('111',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ k1_xboole_0 ) @ X3 ) ) ),
    inference(demod,[status(thm)],['100','105','108','109'])).

thf('112',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','115'])).

thf('117',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','119'])).

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

thf('121',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('126',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) @ sk_B ),
    inference('sup-',[status(thm)],['123','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('134',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X1 )
      | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X0 )
        = X2 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['142'])).

thf('144',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X34: $i,X38: $i] :
      ( ( X38
        = ( k1_tarski @ X34 ) )
      | ( ( sk_C_1 @ X38 @ X34 )
       != X34 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X38 @ X34 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
       != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
       != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_A )
     != sk_A ) ),
    inference('sup-',[status(thm)],['141','147'])).

thf('149',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_A )
 != sk_A ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( sk_A != sk_A )
    | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_A )
      = sk_A )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','150'])).

thf('152',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_A )
      = sk_A ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ( sk_C_1 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_A )
 != sk_A ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('154',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['152','153','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JDNuNpv1XY
% 0.12/0.35  % Computer   : n020.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 13:04:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 53.04/53.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 53.04/53.23  % Solved by: fo/fo7.sh
% 53.04/53.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 53.04/53.23  % done 16017 iterations in 52.757s
% 53.04/53.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 53.04/53.23  % SZS output start Refutation
% 53.04/53.23  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 53.04/53.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 53.04/53.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 53.04/53.23  thf(sk_B_type, type, sk_B: $i).
% 53.04/53.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 53.04/53.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 53.04/53.23  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 53.04/53.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 53.04/53.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 53.04/53.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 53.04/53.23  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 53.04/53.23  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 53.04/53.23  thf(sk_A_type, type, sk_A: $i).
% 53.04/53.23  thf(d1_tarski, axiom,
% 53.04/53.23    (![A:$i,B:$i]:
% 53.04/53.23     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 53.04/53.23       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 53.04/53.23  thf('0', plain,
% 53.04/53.23      (![X34 : $i, X38 : $i]:
% 53.04/53.23         (((X38) = (k1_tarski @ X34))
% 53.04/53.23          | ((sk_C_1 @ X38 @ X34) = (X34))
% 53.04/53.23          | (r2_hidden @ (sk_C_1 @ X38 @ X34) @ X38))),
% 53.04/53.23      inference('cnf', [status(esa)], [d1_tarski])).
% 53.04/53.23  thf(d5_xboole_0, axiom,
% 53.04/53.23    (![A:$i,B:$i,C:$i]:
% 53.04/53.23     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 53.04/53.23       ( ![D:$i]:
% 53.04/53.23         ( ( r2_hidden @ D @ C ) <=>
% 53.04/53.23           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 53.04/53.23  thf('1', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X6 @ X5)
% 53.04/53.23          | (r2_hidden @ X6 @ X3)
% 53.04/53.23          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 53.04/53.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 53.04/53.23  thf('2', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X6 : $i]:
% 53.04/53.23         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['1'])).
% 53.04/53.23  thf('3', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         (((sk_C_1 @ (k4_xboole_0 @ X1 @ X0) @ X2) = (X2))
% 53.04/53.23          | ((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 53.04/53.23          | (r2_hidden @ (sk_C_1 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['0', '2'])).
% 53.04/53.23  thf('4', plain,
% 53.04/53.23      (![X34 : $i, X36 : $i, X37 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X37 @ X36)
% 53.04/53.23          | ((X37) = (X34))
% 53.04/53.23          | ((X36) != (k1_tarski @ X34)))),
% 53.04/53.23      inference('cnf', [status(esa)], [d1_tarski])).
% 53.04/53.23  thf('5', plain,
% 53.04/53.23      (![X34 : $i, X37 : $i]:
% 53.04/53.23         (((X37) = (X34)) | ~ (r2_hidden @ X37 @ (k1_tarski @ X34)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['4'])).
% 53.04/53.23  thf('6', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 53.04/53.23          | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X1))
% 53.04/53.23          | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['3', '5'])).
% 53.04/53.23  thf(t5_boole, axiom,
% 53.04/53.23    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 53.04/53.23  thf('7', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 53.04/53.23      inference('cnf', [status(esa)], [t5_boole])).
% 53.04/53.23  thf(t95_xboole_1, axiom,
% 53.04/53.23    (![A:$i,B:$i]:
% 53.04/53.23     ( ( k3_xboole_0 @ A @ B ) =
% 53.04/53.23       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 53.04/53.23  thf('8', plain,
% 53.04/53.23      (![X20 : $i, X21 : $i]:
% 53.04/53.23         ((k3_xboole_0 @ X20 @ X21)
% 53.04/53.23           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 53.04/53.23              (k2_xboole_0 @ X20 @ X21)))),
% 53.04/53.23      inference('cnf', [status(esa)], [t95_xboole_1])).
% 53.04/53.23  thf(commutativity_k5_xboole_0, axiom,
% 53.04/53.23    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 53.04/53.23  thf('9', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 53.04/53.23      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 53.04/53.23  thf('10', plain,
% 53.04/53.23      (![X20 : $i, X21 : $i]:
% 53.04/53.23         ((k3_xboole_0 @ X20 @ X21)
% 53.04/53.23           = (k5_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ 
% 53.04/53.23              (k5_xboole_0 @ X20 @ X21)))),
% 53.04/53.23      inference('demod', [status(thm)], ['8', '9'])).
% 53.04/53.23  thf('11', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 53.04/53.23           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 53.04/53.23      inference('sup+', [status(thm)], ['7', '10'])).
% 53.04/53.23  thf('12', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 53.04/53.23      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 53.04/53.23  thf('13', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 53.04/53.23           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 53.04/53.23      inference('demod', [status(thm)], ['11', '12'])).
% 53.04/53.23  thf(t92_xboole_1, axiom,
% 53.04/53.23    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 53.04/53.23  thf('14', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 53.04/53.23      inference('cnf', [status(esa)], [t92_xboole_1])).
% 53.04/53.23  thf(t91_xboole_1, axiom,
% 53.04/53.23    (![A:$i,B:$i,C:$i]:
% 53.04/53.23     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 53.04/53.23       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 53.04/53.23  thf('15', plain,
% 53.04/53.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 53.04/53.23         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 53.04/53.23           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 53.04/53.23      inference('cnf', [status(esa)], [t91_xboole_1])).
% 53.04/53.23  thf('16', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 53.04/53.23           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 53.04/53.23      inference('sup+', [status(thm)], ['14', '15'])).
% 53.04/53.23  thf('17', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 53.04/53.23      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 53.04/53.23  thf('18', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 53.04/53.23      inference('cnf', [status(esa)], [t5_boole])).
% 53.04/53.23  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 53.04/53.23      inference('sup+', [status(thm)], ['17', '18'])).
% 53.04/53.23  thf('20', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 53.04/53.23      inference('demod', [status(thm)], ['16', '19'])).
% 53.04/53.23  thf('21', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 53.04/53.23           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 53.04/53.23      inference('sup+', [status(thm)], ['13', '20'])).
% 53.04/53.23  thf(t100_xboole_1, axiom,
% 53.04/53.23    (![A:$i,B:$i]:
% 53.04/53.23     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 53.04/53.23  thf('22', plain,
% 53.04/53.23      (![X12 : $i, X13 : $i]:
% 53.04/53.23         ((k4_xboole_0 @ X12 @ X13)
% 53.04/53.23           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 53.04/53.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 53.04/53.23  thf('23', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 53.04/53.23      inference('demod', [status(thm)], ['21', '22'])).
% 53.04/53.23  thf('24', plain,
% 53.04/53.23      (![X34 : $i, X35 : $i, X36 : $i]:
% 53.04/53.23         (((X35) != (X34))
% 53.04/53.23          | (r2_hidden @ X35 @ X36)
% 53.04/53.23          | ((X36) != (k1_tarski @ X34)))),
% 53.04/53.23      inference('cnf', [status(esa)], [d1_tarski])).
% 53.04/53.23  thf('25', plain, (![X34 : $i]: (r2_hidden @ X34 @ (k1_tarski @ X34))),
% 53.04/53.23      inference('simplify', [status(thm)], ['24'])).
% 53.04/53.23  thf('26', plain,
% 53.04/53.23      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X2 @ X3)
% 53.04/53.23          | (r2_hidden @ X2 @ X4)
% 53.04/53.23          | (r2_hidden @ X2 @ X5)
% 53.04/53.23          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 53.04/53.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 53.04/53.23  thf('27', plain,
% 53.04/53.23      (![X2 : $i, X3 : $i, X4 : $i]:
% 53.04/53.23         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 53.04/53.23          | (r2_hidden @ X2 @ X4)
% 53.04/53.23          | ~ (r2_hidden @ X2 @ X3))),
% 53.04/53.23      inference('simplify', [status(thm)], ['26'])).
% 53.04/53.23  thf('28', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r2_hidden @ X0 @ X1)
% 53.04/53.23          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['25', '27'])).
% 53.04/53.23  thf('29', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 53.04/53.23          | (r2_hidden @ X0 @ k1_xboole_0))),
% 53.04/53.23      inference('sup+', [status(thm)], ['23', '28'])).
% 53.04/53.23  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 53.04/53.23  thf('30', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 53.04/53.23      inference('cnf', [status(esa)], [t65_xboole_1])).
% 53.04/53.23  thf('31', plain, (![X34 : $i]: (r2_hidden @ X34 @ (k1_tarski @ X34))),
% 53.04/53.23      inference('simplify', [status(thm)], ['24'])).
% 53.04/53.23  thf(t3_xboole_0, axiom,
% 53.04/53.23    (![A:$i,B:$i]:
% 53.04/53.23     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 53.04/53.23            ( r1_xboole_0 @ A @ B ) ) ) & 
% 53.04/53.23       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 53.04/53.23            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 53.04/53.23  thf('32', plain,
% 53.04/53.23      (![X8 : $i, X10 : $i, X11 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X10 @ X8)
% 53.04/53.23          | ~ (r2_hidden @ X10 @ X11)
% 53.04/53.23          | ~ (r1_xboole_0 @ X8 @ X11))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('33', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['31', '32'])).
% 53.04/53.23  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 53.04/53.23      inference('sup-', [status(thm)], ['30', '33'])).
% 53.04/53.23  thf('35', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 53.04/53.23      inference('clc', [status(thm)], ['29', '34'])).
% 53.04/53.23  thf('36', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('37', plain,
% 53.04/53.23      (![X34 : $i, X37 : $i]:
% 53.04/53.23         (((X37) = (X34)) | ~ (r2_hidden @ X37 @ (k1_tarski @ X34)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['4'])).
% 53.04/53.23  thf('38', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 53.04/53.23          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['36', '37'])).
% 53.04/53.23  thf('39', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('40', plain,
% 53.04/53.23      (![X2 : $i, X3 : $i, X4 : $i]:
% 53.04/53.23         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 53.04/53.23          | (r2_hidden @ X2 @ X4)
% 53.04/53.23          | ~ (r2_hidden @ X2 @ X3))),
% 53.04/53.23      inference('simplify', [status(thm)], ['26'])).
% 53.04/53.23  thf('41', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X0 @ X1)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['39', '40'])).
% 53.04/53.23  thf('42', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 53.04/53.23          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X2 @ (k1_tarski @ X0)) @ X1)
% 53.04/53.23          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2))),
% 53.04/53.23      inference('sup+', [status(thm)], ['38', '41'])).
% 53.04/53.23  thf('43', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r2_hidden @ (sk_C @ X2 @ (k1_tarski @ X0)) @ X1)
% 53.04/53.23          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 53.04/53.23          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['42'])).
% 53.04/53.23  thf('44', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('45', plain,
% 53.04/53.23      (![X34 : $i, X37 : $i]:
% 53.04/53.23         (((X37) = (X34)) | ~ (r2_hidden @ X37 @ (k1_tarski @ X34)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['4'])).
% 53.04/53.23  thf('46', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 53.04/53.23          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['44', '45'])).
% 53.04/53.23  thf('47', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 53.04/53.23      inference('demod', [status(thm)], ['21', '22'])).
% 53.04/53.23  thf('48', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X0 @ X1)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['39', '40'])).
% 53.04/53.23  thf('49', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 53.04/53.23          | (r2_hidden @ (sk_C @ X1 @ X0) @ k1_xboole_0)
% 53.04/53.23          | (r1_xboole_0 @ X0 @ X1))),
% 53.04/53.23      inference('sup+', [status(thm)], ['47', '48'])).
% 53.04/53.23  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 53.04/53.23      inference('sup-', [status(thm)], ['30', '33'])).
% 53.04/53.23  thf('51', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X0 @ X1)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 53.04/53.23      inference('clc', [status(thm)], ['49', '50'])).
% 53.04/53.23  thf('52', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ k1_xboole_0))
% 53.04/53.23          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 53.04/53.23          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 53.04/53.23      inference('sup+', [status(thm)], ['46', '51'])).
% 53.04/53.23  thf('53', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 53.04/53.23          | (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['52'])).
% 53.04/53.23  thf('54', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 53.04/53.23      inference('demod', [status(thm)], ['21', '22'])).
% 53.04/53.23  thf('55', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('56', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X6 : $i]:
% 53.04/53.23         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['1'])).
% 53.04/53.23  thf('57', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['55', '56'])).
% 53.04/53.23  thf('58', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('59', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X6 @ X5)
% 53.04/53.23          | ~ (r2_hidden @ X6 @ X4)
% 53.04/53.23          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 53.04/53.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 53.04/53.23  thf('60', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X6 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X6 @ X4)
% 53.04/53.23          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['59'])).
% 53.04/53.23  thf('61', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 53.04/53.23          | ~ (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['58', '60'])).
% 53.04/53.23  thf('62', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 53.04/53.23          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['57', '61'])).
% 53.04/53.23  thf('63', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 53.04/53.23      inference('simplify', [status(thm)], ['62'])).
% 53.04/53.23  thf('64', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 53.04/53.23          (k4_xboole_0 @ X1 @ X0))),
% 53.04/53.23      inference('sup+', [status(thm)], ['54', '63'])).
% 53.04/53.23  thf('65', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('66', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('67', plain,
% 53.04/53.23      (![X8 : $i, X10 : $i, X11 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X10 @ X8)
% 53.04/53.23          | ~ (r2_hidden @ X10 @ X11)
% 53.04/53.23          | ~ (r1_xboole_0 @ X8 @ X11))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('68', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X1 @ X0)
% 53.04/53.23          | ~ (r1_xboole_0 @ X0 @ X2)
% 53.04/53.23          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 53.04/53.23      inference('sup-', [status(thm)], ['66', '67'])).
% 53.04/53.23  thf('69', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X0 @ X1)
% 53.04/53.23          | ~ (r1_xboole_0 @ X1 @ X0)
% 53.04/53.23          | (r1_xboole_0 @ X0 @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['65', '68'])).
% 53.04/53.23  thf('70', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 53.04/53.23      inference('simplify', [status(thm)], ['69'])).
% 53.04/53.23  thf('71', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 53.04/53.23          (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['64', '70'])).
% 53.04/53.23  thf('72', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 53.04/53.23          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['44', '45'])).
% 53.04/53.23  thf('73', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('74', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r2_hidden @ X0 @ X1)
% 53.04/53.23          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 53.04/53.23          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 53.04/53.23      inference('sup+', [status(thm)], ['72', '73'])).
% 53.04/53.23  thf('75', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 53.04/53.23      inference('simplify', [status(thm)], ['74'])).
% 53.04/53.23  thf('76', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['55', '56'])).
% 53.04/53.23  thf('77', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X1 @ X0)
% 53.04/53.23          | ~ (r1_xboole_0 @ X0 @ X2)
% 53.04/53.23          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 53.04/53.23      inference('sup-', [status(thm)], ['66', '67'])).
% 53.04/53.23  thf('78', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 53.04/53.23          | ~ (r1_xboole_0 @ X2 @ X0)
% 53.04/53.23          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 53.04/53.23      inference('sup-', [status(thm)], ['76', '77'])).
% 53.04/53.23  thf('79', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         (~ (r1_xboole_0 @ X2 @ X0)
% 53.04/53.23          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 53.04/53.23      inference('simplify', [status(thm)], ['78'])).
% 53.04/53.23  thf('80', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r2_hidden @ X0 @ X1)
% 53.04/53.23          | (r1_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['75', '79'])).
% 53.04/53.23  thf('81', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X7 : $i]:
% 53.04/53.23         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 53.04/53.23          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 53.04/53.23          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 53.04/53.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 53.04/53.23  thf('82', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X6 : $i]:
% 53.04/53.23         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['1'])).
% 53.04/53.23  thf('83', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 53.04/53.23         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 53.04/53.23          | ((X3) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 53.04/53.23          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['81', '82'])).
% 53.04/53.23  thf('84', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['55', '56'])).
% 53.04/53.23  thf('85', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('86', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X6 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X6 @ X4)
% 53.04/53.23          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['59'])).
% 53.04/53.23  thf('87', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 53.04/53.23          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['85', '86'])).
% 53.04/53.23  thf('88', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 53.04/53.23          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['84', '87'])).
% 53.04/53.23  thf('89', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 53.04/53.23      inference('simplify', [status(thm)], ['88'])).
% 53.04/53.23  thf('90', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 53.04/53.23      inference('simplify', [status(thm)], ['69'])).
% 53.04/53.23  thf('91', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['89', '90'])).
% 53.04/53.23  thf('92', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 53.04/53.23      inference('demod', [status(thm)], ['21', '22'])).
% 53.04/53.23  thf('93', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r2_hidden @ X0 @ X1)
% 53.04/53.23          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['25', '27'])).
% 53.04/53.23  thf('94', plain,
% 53.04/53.23      (![X8 : $i, X10 : $i, X11 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X10 @ X8)
% 53.04/53.23          | ~ (r2_hidden @ X10 @ X11)
% 53.04/53.23          | ~ (r1_xboole_0 @ X8 @ X11))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('95', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r2_hidden @ X1 @ X0)
% 53.04/53.23          | ~ (r1_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0) @ X2)
% 53.04/53.23          | ~ (r2_hidden @ X1 @ X2))),
% 53.04/53.23      inference('sup-', [status(thm)], ['93', '94'])).
% 53.04/53.23  thf('96', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r1_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) @ X1)
% 53.04/53.23          | ~ (r2_hidden @ X0 @ X1)
% 53.04/53.23          | (r2_hidden @ X0 @ k1_xboole_0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['92', '95'])).
% 53.04/53.23  thf('97', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 53.04/53.23      inference('sup-', [status(thm)], ['30', '33'])).
% 53.04/53.23  thf('98', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X0 @ X1)
% 53.04/53.23          | ~ (r1_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) @ 
% 53.04/53.23               X1))),
% 53.04/53.23      inference('clc', [status(thm)], ['96', '97'])).
% 53.04/53.23  thf('99', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['91', '98'])).
% 53.04/53.23  thf('100', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 53.04/53.23         (((X3)
% 53.04/53.23            = (k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) @ X2))
% 53.04/53.23          | (r2_hidden @ 
% 53.04/53.23             (sk_D @ X3 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)) @ 
% 53.04/53.23             X3))),
% 53.04/53.23      inference('sup-', [status(thm)], ['83', '99'])).
% 53.04/53.23  thf('101', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X7 : $i]:
% 53.04/53.23         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 53.04/53.23          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 53.04/53.23          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 53.04/53.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 53.04/53.23  thf('102', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 53.04/53.23      inference('sup-', [status(thm)], ['30', '33'])).
% 53.04/53.23  thf('103', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 53.04/53.23          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['101', '102'])).
% 53.04/53.23  thf('104', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['91', '98'])).
% 53.04/53.23  thf('105', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['103', '104'])).
% 53.04/53.23  thf('106', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 53.04/53.23          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['101', '102'])).
% 53.04/53.23  thf('107', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 53.04/53.23      inference('sup-', [status(thm)], ['30', '33'])).
% 53.04/53.23  thf('108', plain,
% 53.04/53.23      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['106', '107'])).
% 53.04/53.23  thf('109', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['103', '104'])).
% 53.04/53.23  thf('110', plain,
% 53.04/53.23      (![X2 : $i, X3 : $i]:
% 53.04/53.23         (((X3) = (k1_xboole_0))
% 53.04/53.23          | (r2_hidden @ (sk_D @ X3 @ X2 @ k1_xboole_0) @ X3))),
% 53.04/53.23      inference('demod', [status(thm)], ['100', '105', '108', '109'])).
% 53.04/53.23  thf('111', plain,
% 53.04/53.23      (![X2 : $i, X3 : $i]:
% 53.04/53.23         (((X3) = (k1_xboole_0))
% 53.04/53.23          | (r2_hidden @ (sk_D @ X3 @ X2 @ k1_xboole_0) @ X3))),
% 53.04/53.23      inference('demod', [status(thm)], ['100', '105', '108', '109'])).
% 53.04/53.23  thf('112', plain,
% 53.04/53.23      (![X8 : $i, X10 : $i, X11 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X10 @ X8)
% 53.04/53.23          | ~ (r2_hidden @ X10 @ X11)
% 53.04/53.23          | ~ (r1_xboole_0 @ X8 @ X11))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('113', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         (((X0) = (k1_xboole_0))
% 53.04/53.23          | ~ (r1_xboole_0 @ X0 @ X2)
% 53.04/53.23          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ X2))),
% 53.04/53.23      inference('sup-', [status(thm)], ['111', '112'])).
% 53.04/53.23  thf('114', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         (((X0) = (k1_xboole_0))
% 53.04/53.23          | ~ (r1_xboole_0 @ X0 @ X0)
% 53.04/53.23          | ((X0) = (k1_xboole_0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['110', '113'])).
% 53.04/53.23  thf('115', plain,
% 53.04/53.23      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['114'])).
% 53.04/53.23  thf('116', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 53.04/53.23          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['80', '115'])).
% 53.04/53.23  thf('117', plain,
% 53.04/53.23      (![X8 : $i, X10 : $i, X11 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X10 @ X8)
% 53.04/53.23          | ~ (r2_hidden @ X10 @ X11)
% 53.04/53.23          | ~ (r1_xboole_0 @ X8 @ X11))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('118', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 53.04/53.23          | ~ (r1_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0) @ X2)
% 53.04/53.23          | ~ (r2_hidden @ X1 @ X2))),
% 53.04/53.23      inference('sup-', [status(thm)], ['116', '117'])).
% 53.04/53.23  thf('119', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 53.04/53.23          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['71', '118'])).
% 53.04/53.23  thf('120', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1))
% 53.04/53.23          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['53', '119'])).
% 53.04/53.23  thf(t69_zfmisc_1, conjecture,
% 53.04/53.23    (![A:$i,B:$i]:
% 53.04/53.23     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 53.04/53.23       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 53.04/53.23  thf(zf_stmt_0, negated_conjecture,
% 53.04/53.23    (~( ![A:$i,B:$i]:
% 53.04/53.23        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 53.04/53.23          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 53.04/53.23    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 53.04/53.23  thf('121', plain,
% 53.04/53.23      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 53.04/53.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.04/53.23  thf('122', plain,
% 53.04/53.23      ((((k1_xboole_0) != (k1_xboole_0))
% 53.04/53.23        | (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['120', '121'])).
% 53.04/53.23  thf('123', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A))),
% 53.04/53.23      inference('simplify', [status(thm)], ['122'])).
% 53.04/53.23  thf('124', plain,
% 53.04/53.23      (![X8 : $i, X9 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('125', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 53.04/53.23      inference('demod', [status(thm)], ['21', '22'])).
% 53.04/53.23  thf('126', plain,
% 53.04/53.23      (![X3 : $i, X4 : $i, X6 : $i]:
% 53.04/53.23         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['1'])).
% 53.04/53.23  thf('127', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 53.04/53.23          | (r2_hidden @ X1 @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['125', '126'])).
% 53.04/53.23  thf('128', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)) @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['124', '127'])).
% 53.04/53.23  thf('129', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X1 @ X0)
% 53.04/53.23          | ~ (r1_xboole_0 @ X0 @ X2)
% 53.04/53.23          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 53.04/53.23      inference('sup-', [status(thm)], ['66', '67'])).
% 53.04/53.23  thf('130', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 53.04/53.23          | ~ (r1_xboole_0 @ X1 @ X0)
% 53.04/53.23          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['128', '129'])).
% 53.04/53.23  thf('131', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r1_xboole_0 @ X1 @ X0)
% 53.04/53.23          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 53.04/53.23      inference('simplify', [status(thm)], ['130'])).
% 53.04/53.23  thf('132', plain,
% 53.04/53.23      ((r1_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) @ sk_B)),
% 53.04/53.23      inference('sup-', [status(thm)], ['123', '131'])).
% 53.04/53.23  thf('133', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X0 @ X1)
% 53.04/53.23          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 53.04/53.23      inference('clc', [status(thm)], ['49', '50'])).
% 53.04/53.23  thf('134', plain,
% 53.04/53.23      (![X8 : $i, X10 : $i, X11 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X10 @ X8)
% 53.04/53.23          | ~ (r2_hidden @ X10 @ X11)
% 53.04/53.23          | ~ (r1_xboole_0 @ X8 @ X11))),
% 53.04/53.23      inference('cnf', [status(esa)], [t3_xboole_0])).
% 53.04/53.23  thf('135', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ X0 @ X1)
% 53.04/53.23          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X2)
% 53.04/53.23          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 53.04/53.23      inference('sup-', [status(thm)], ['133', '134'])).
% 53.04/53.23  thf('136', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         (~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ sk_B)
% 53.04/53.23          | (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['132', '135'])).
% 53.04/53.23  thf('137', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 53.04/53.23          | (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 53.04/53.23          | (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['43', '136'])).
% 53.04/53.23  thf('138', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((r1_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 53.04/53.23          | (r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['137'])).
% 53.04/53.23  thf('139', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 53.04/53.23      inference('sup-', [status(thm)], ['31', '32'])).
% 53.04/53.23  thf('140', plain,
% 53.04/53.23      (![X0 : $i]:
% 53.04/53.23         ((r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 53.04/53.23          | ~ (r2_hidden @ sk_A @ X0))),
% 53.04/53.23      inference('sup-', [status(thm)], ['138', '139'])).
% 53.04/53.23  thf('141', plain,
% 53.04/53.23      ((r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 53.04/53.23      inference('sup-', [status(thm)], ['35', '140'])).
% 53.04/53.23  thf('142', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 53.04/53.23          | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X1))
% 53.04/53.23          | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['3', '5'])).
% 53.04/53.23  thf('143', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 53.04/53.23         (((X0) != (X2))
% 53.04/53.23          | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X0) = (X2))
% 53.04/53.23          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X0)))),
% 53.04/53.23      inference('eq_fact', [status(thm)], ['142'])).
% 53.04/53.23  thf('144', plain,
% 53.04/53.23      (![X1 : $i, X2 : $i]:
% 53.04/53.23         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 53.04/53.23          | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['143'])).
% 53.04/53.23  thf('145', plain,
% 53.04/53.23      (![X34 : $i, X38 : $i]:
% 53.04/53.23         (((X38) = (k1_tarski @ X34))
% 53.04/53.23          | ((sk_C_1 @ X38 @ X34) != (X34))
% 53.04/53.23          | ~ (r2_hidden @ (sk_C_1 @ X38 @ X34) @ X38))),
% 53.04/53.23      inference('cnf', [status(esa)], [d1_tarski])).
% 53.04/53.23  thf('146', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 53.04/53.23          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 53.04/53.23          | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 53.04/53.23          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['144', '145'])).
% 53.04/53.23  thf('147', plain,
% 53.04/53.23      (![X0 : $i, X1 : $i]:
% 53.04/53.23         (((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 53.04/53.23          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 53.04/53.23          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['146'])).
% 53.04/53.23  thf('148', plain,
% 53.04/53.23      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))
% 53.04/53.23        | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_A)
% 53.04/53.23            != (sk_A)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['141', '147'])).
% 53.04/53.23  thf('149', plain,
% 53.04/53.23      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 53.04/53.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.04/53.23  thf('150', plain,
% 53.04/53.23      (((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_A) != (sk_A))),
% 53.04/53.23      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 53.04/53.23  thf('151', plain,
% 53.04/53.23      ((((sk_A) != (sk_A))
% 53.04/53.23        | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_A) = (sk_A))
% 53.04/53.23        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 53.04/53.23      inference('sup-', [status(thm)], ['6', '150'])).
% 53.04/53.23  thf('152', plain,
% 53.04/53.23      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))
% 53.04/53.23        | ((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_A) = (sk_A)))),
% 53.04/53.23      inference('simplify', [status(thm)], ['151'])).
% 53.04/53.23  thf('153', plain,
% 53.04/53.23      (((sk_C_1 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_A) != (sk_A))),
% 53.04/53.23      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 53.04/53.23  thf('154', plain,
% 53.04/53.23      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 53.04/53.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.04/53.23  thf('155', plain, ($false),
% 53.04/53.23      inference('simplify_reflect-', [status(thm)], ['152', '153', '154'])).
% 53.04/53.23  
% 53.04/53.23  % SZS output end Refutation
% 53.04/53.23  
% 53.04/53.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
