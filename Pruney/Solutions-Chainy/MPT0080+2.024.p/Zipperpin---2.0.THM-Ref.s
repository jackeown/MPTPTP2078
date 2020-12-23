%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JPGKSxcyIT

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:07 EST 2020

% Result     : Theorem 2.84s
% Output     : Refutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 131 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   18
%              Number of atoms          :  673 (1110 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

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

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

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
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k2_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('46',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('67',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JPGKSxcyIT
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:56:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 2.84/3.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.84/3.05  % Solved by: fo/fo7.sh
% 2.84/3.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.84/3.05  % done 6917 iterations in 2.598s
% 2.84/3.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.84/3.05  % SZS output start Refutation
% 2.84/3.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.84/3.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.84/3.05  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.84/3.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.84/3.05  thf(sk_A_type, type, sk_A: $i).
% 2.84/3.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.84/3.05  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.84/3.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.84/3.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.84/3.05  thf(sk_B_type, type, sk_B: $i).
% 2.84/3.05  thf(t73_xboole_1, conjecture,
% 2.84/3.05    (![A:$i,B:$i,C:$i]:
% 2.84/3.05     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.84/3.05       ( r1_tarski @ A @ B ) ))).
% 2.84/3.05  thf(zf_stmt_0, negated_conjecture,
% 2.84/3.05    (~( ![A:$i,B:$i,C:$i]:
% 2.84/3.05        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 2.84/3.05            ( r1_xboole_0 @ A @ C ) ) =>
% 2.84/3.05          ( r1_tarski @ A @ B ) ) )),
% 2.84/3.05    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 2.84/3.05  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 2.84/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.84/3.05  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 2.84/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.84/3.05  thf(symmetry_r1_xboole_0, axiom,
% 2.84/3.05    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.84/3.05  thf('2', plain,
% 2.84/3.05      (![X12 : $i, X13 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X12 @ X13) | ~ (r1_xboole_0 @ X13 @ X12))),
% 2.84/3.05      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.84/3.05  thf('3', plain, ((r1_xboole_0 @ sk_C_2 @ sk_A)),
% 2.84/3.05      inference('sup-', [status(thm)], ['1', '2'])).
% 2.84/3.05  thf(d3_tarski, axiom,
% 2.84/3.05    (![A:$i,B:$i]:
% 2.84/3.05     ( ( r1_tarski @ A @ B ) <=>
% 2.84/3.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.84/3.05  thf('4', plain,
% 2.84/3.05      (![X3 : $i, X5 : $i]:
% 2.84/3.05         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.84/3.05      inference('cnf', [status(esa)], [d3_tarski])).
% 2.84/3.05  thf(d5_xboole_0, axiom,
% 2.84/3.05    (![A:$i,B:$i,C:$i]:
% 2.84/3.05     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.84/3.05       ( ![D:$i]:
% 2.84/3.05         ( ( r2_hidden @ D @ C ) <=>
% 2.84/3.05           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.84/3.05  thf('5', plain,
% 2.84/3.05      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.84/3.05         (~ (r2_hidden @ X10 @ X9)
% 2.84/3.05          | (r2_hidden @ X10 @ X7)
% 2.84/3.05          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 2.84/3.05      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.84/3.05  thf('6', plain,
% 2.84/3.05      (![X7 : $i, X8 : $i, X10 : $i]:
% 2.84/3.05         ((r2_hidden @ X10 @ X7)
% 2.84/3.05          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 2.84/3.05      inference('simplify', [status(thm)], ['5'])).
% 2.84/3.05  thf('7', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.84/3.05          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 2.84/3.05      inference('sup-', [status(thm)], ['4', '6'])).
% 2.84/3.05  thf('8', plain,
% 2.84/3.05      (![X3 : $i, X5 : $i]:
% 2.84/3.05         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 2.84/3.05      inference('cnf', [status(esa)], [d3_tarski])).
% 2.84/3.05  thf('9', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]:
% 2.84/3.05         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 2.84/3.05          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 2.84/3.05      inference('sup-', [status(thm)], ['7', '8'])).
% 2.84/3.05  thf('10', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 2.84/3.05      inference('simplify', [status(thm)], ['9'])).
% 2.84/3.05  thf(t12_xboole_1, axiom,
% 2.84/3.05    (![A:$i,B:$i]:
% 2.84/3.05     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.84/3.05  thf('11', plain,
% 2.84/3.05      (![X18 : $i, X19 : $i]:
% 2.84/3.05         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 2.84/3.05      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.84/3.05  thf('12', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]:
% 2.84/3.05         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.84/3.05      inference('sup-', [status(thm)], ['10', '11'])).
% 2.84/3.05  thf(commutativity_k2_xboole_0, axiom,
% 2.84/3.05    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.84/3.05  thf('13', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.05  thf('14', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]:
% 2.84/3.05         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.84/3.05      inference('demod', [status(thm)], ['12', '13'])).
% 2.84/3.05  thf('15', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.05  thf(t3_xboole_0, axiom,
% 2.84/3.05    (![A:$i,B:$i]:
% 2.84/3.05     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.84/3.05            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.84/3.05       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.84/3.05            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.84/3.05  thf('16', plain,
% 2.84/3.05      (![X14 : $i, X15 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X14))),
% 2.84/3.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.84/3.05  thf(t7_xboole_1, axiom,
% 2.84/3.05    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.84/3.05  thf('17', plain,
% 2.84/3.05      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 2.84/3.05      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.84/3.05  thf('18', plain,
% 2.84/3.05      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.84/3.05         (~ (r2_hidden @ X2 @ X3)
% 2.84/3.05          | (r2_hidden @ X2 @ X4)
% 2.84/3.05          | ~ (r1_tarski @ X3 @ X4))),
% 2.84/3.05      inference('cnf', [status(esa)], [d3_tarski])).
% 2.84/3.05  thf('19', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 2.84/3.05      inference('sup-', [status(thm)], ['17', '18'])).
% 2.84/3.05  thf('20', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X0 @ X1)
% 2.84/3.05          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 2.84/3.05      inference('sup-', [status(thm)], ['16', '19'])).
% 2.84/3.05  thf('21', plain,
% 2.84/3.05      (![X14 : $i, X15 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X15))),
% 2.84/3.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.84/3.05  thf('22', plain,
% 2.84/3.05      (![X14 : $i, X16 : $i, X17 : $i]:
% 2.84/3.05         (~ (r2_hidden @ X16 @ X14)
% 2.84/3.05          | ~ (r2_hidden @ X16 @ X17)
% 2.84/3.05          | ~ (r1_xboole_0 @ X14 @ X17))),
% 2.84/3.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.84/3.05  thf('23', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X1 @ X0)
% 2.84/3.05          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.84/3.05          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['21', '22'])).
% 2.84/3.05  thf('24', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X1 @ X2)
% 2.84/3.05          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.84/3.05          | (r1_xboole_0 @ X1 @ X2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['20', '23'])).
% 2.84/3.05  thf('25', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.84/3.05          | (r1_xboole_0 @ X1 @ X2))),
% 2.84/3.05      inference('simplify', [status(thm)], ['24'])).
% 2.84/3.05  thf('26', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.84/3.05          | (r1_xboole_0 @ X0 @ X2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['15', '25'])).
% 2.84/3.05  thf('27', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         (~ (r1_xboole_0 @ X2 @ X0)
% 2.84/3.05          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['14', '26'])).
% 2.84/3.05  thf('28', plain,
% 2.84/3.05      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C_2)),
% 2.84/3.05      inference('sup-', [status(thm)], ['3', '27'])).
% 2.84/3.05  thf('29', plain,
% 2.84/3.05      (![X14 : $i, X15 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X15))),
% 2.84/3.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.84/3.05  thf('30', plain,
% 2.84/3.05      (![X14 : $i, X15 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X14))),
% 2.84/3.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.84/3.05  thf('31', plain,
% 2.84/3.05      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.84/3.05         (~ (r2_hidden @ X10 @ X9)
% 2.84/3.05          | ~ (r2_hidden @ X10 @ X8)
% 2.84/3.05          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 2.84/3.05      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.84/3.05  thf('32', plain,
% 2.84/3.05      (![X7 : $i, X8 : $i, X10 : $i]:
% 2.84/3.05         (~ (r2_hidden @ X10 @ X8)
% 2.84/3.05          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 2.84/3.05      inference('simplify', [status(thm)], ['31'])).
% 2.84/3.05  thf('33', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.84/3.05          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 2.84/3.05      inference('sup-', [status(thm)], ['30', '32'])).
% 2.84/3.05  thf('34', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 2.84/3.05          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 2.84/3.05      inference('sup-', [status(thm)], ['29', '33'])).
% 2.84/3.05  thf('35', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 2.84/3.05      inference('simplify', [status(thm)], ['34'])).
% 2.84/3.05  thf(t70_xboole_1, axiom,
% 2.84/3.05    (![A:$i,B:$i,C:$i]:
% 2.84/3.05     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.84/3.05            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.84/3.05       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.84/3.05            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.84/3.05  thf('36', plain,
% 2.84/3.05      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 2.84/3.05          | ~ (r1_xboole_0 @ X22 @ X23)
% 2.84/3.05          | ~ (r1_xboole_0 @ X22 @ X24))),
% 2.84/3.05      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.84/3.05  thf('37', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.84/3.05          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 2.84/3.05      inference('sup-', [status(thm)], ['35', '36'])).
% 2.84/3.05  thf('38', plain,
% 2.84/3.05      (![X0 : $i]:
% 2.84/3.05         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ (k2_xboole_0 @ X0 @ sk_C_2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['28', '37'])).
% 2.84/3.05  thf('39', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 2.84/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.84/3.05  thf('40', plain,
% 2.84/3.05      (![X18 : $i, X19 : $i]:
% 2.84/3.05         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 2.84/3.05      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.84/3.05  thf('41', plain,
% 2.84/3.05      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 2.84/3.05         = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['39', '40'])).
% 2.84/3.05  thf('42', plain,
% 2.84/3.05      (![X22 : $i, X23 : $i, X25 : $i]:
% 2.84/3.05         ((r1_xboole_0 @ X22 @ X23)
% 2.84/3.05          | ~ (r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X25)))),
% 2.84/3.05      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.84/3.05  thf('43', plain,
% 2.84/3.05      (![X0 : $i]:
% 2.84/3.05         (~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 2.84/3.05          | (r1_xboole_0 @ X0 @ sk_A))),
% 2.84/3.05      inference('sup-', [status(thm)], ['41', '42'])).
% 2.84/3.05  thf('44', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 2.84/3.05      inference('sup-', [status(thm)], ['38', '43'])).
% 2.84/3.05  thf('45', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.84/3.05          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 2.84/3.05      inference('sup-', [status(thm)], ['35', '36'])).
% 2.84/3.05  thf('46', plain,
% 2.84/3.05      ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ sk_A))),
% 2.84/3.05      inference('sup-', [status(thm)], ['44', '45'])).
% 2.84/3.05  thf(t39_xboole_1, axiom,
% 2.84/3.05    (![A:$i,B:$i]:
% 2.84/3.05     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.84/3.05  thf('47', plain,
% 2.84/3.05      (![X20 : $i, X21 : $i]:
% 2.84/3.05         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 2.84/3.05           = (k2_xboole_0 @ X20 @ X21))),
% 2.84/3.05      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.84/3.05  thf('48', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.05  thf('49', plain,
% 2.84/3.05      (![X3 : $i, X5 : $i]:
% 2.84/3.05         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.84/3.05      inference('cnf', [status(esa)], [d3_tarski])).
% 2.84/3.05  thf('50', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 2.84/3.05      inference('sup-', [status(thm)], ['17', '18'])).
% 2.84/3.05  thf('51', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r1_tarski @ X0 @ X1)
% 2.84/3.05          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 2.84/3.05      inference('sup-', [status(thm)], ['49', '50'])).
% 2.84/3.05  thf('52', plain,
% 2.84/3.05      (![X3 : $i, X5 : $i]:
% 2.84/3.05         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 2.84/3.05      inference('cnf', [status(esa)], [d3_tarski])).
% 2.84/3.05  thf('53', plain,
% 2.84/3.05      (![X14 : $i, X16 : $i, X17 : $i]:
% 2.84/3.05         (~ (r2_hidden @ X16 @ X14)
% 2.84/3.05          | ~ (r2_hidden @ X16 @ X17)
% 2.84/3.05          | ~ (r1_xboole_0 @ X14 @ X17))),
% 2.84/3.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.84/3.05  thf('54', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r1_tarski @ X0 @ X1)
% 2.84/3.05          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.84/3.05          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['52', '53'])).
% 2.84/3.05  thf('55', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         ((r1_tarski @ X1 @ X2)
% 2.84/3.05          | ~ (r1_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 2.84/3.05          | (r1_tarski @ X1 @ X2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['51', '54'])).
% 2.84/3.05  thf('56', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         (~ (r1_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 2.84/3.05          | (r1_tarski @ X1 @ X2))),
% 2.84/3.05      inference('simplify', [status(thm)], ['55'])).
% 2.84/3.05  thf('57', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         (~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 2.84/3.05          | (r1_tarski @ X0 @ X2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['48', '56'])).
% 2.84/3.05  thf('58', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.05         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 2.84/3.05          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 2.84/3.05      inference('sup-', [status(thm)], ['47', '57'])).
% 2.84/3.05  thf('59', plain,
% 2.84/3.05      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 2.84/3.05      inference('sup-', [status(thm)], ['46', '58'])).
% 2.84/3.05  thf('60', plain,
% 2.84/3.05      (![X18 : $i, X19 : $i]:
% 2.84/3.05         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 2.84/3.05      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.84/3.05  thf('61', plain,
% 2.84/3.05      (![X0 : $i]: ((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) = (X0))),
% 2.84/3.05      inference('sup-', [status(thm)], ['59', '60'])).
% 2.84/3.05  thf('62', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.05  thf('63', plain,
% 2.84/3.05      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (X0))),
% 2.84/3.05      inference('sup+', [status(thm)], ['61', '62'])).
% 2.84/3.05  thf('64', plain,
% 2.84/3.05      (![X20 : $i, X21 : $i]:
% 2.84/3.05         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 2.84/3.05           = (k2_xboole_0 @ X20 @ X21))),
% 2.84/3.05      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.84/3.05  thf('65', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 2.84/3.05      inference('sup+', [status(thm)], ['63', '64'])).
% 2.84/3.05  thf('66', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.05  thf('67', plain,
% 2.84/3.05      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 2.84/3.05      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.84/3.05  thf('68', plain,
% 2.84/3.05      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.84/3.05      inference('sup+', [status(thm)], ['66', '67'])).
% 2.84/3.05  thf('69', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.84/3.05      inference('sup+', [status(thm)], ['65', '68'])).
% 2.84/3.05  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 2.84/3.05  
% 2.84/3.05  % SZS output end Refutation
% 2.84/3.05  
% 2.84/3.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
