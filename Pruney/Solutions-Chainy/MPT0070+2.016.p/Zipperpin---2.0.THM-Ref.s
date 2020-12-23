%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v0udYHArZU

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:34 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 501 expanded)
%              Number of leaves         :   21 ( 163 expanded)
%              Depth                    :   22
%              Number of atoms          :  936 (3895 expanded)
%              Number of equality atoms :   77 ( 330 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['37','38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = sk_B ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['37','38','41'])).

thf('64',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','64'])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('68',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','54'])).

thf('72',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('73',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_B ) @ k1_xboole_0 )
    = sk_B ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('78',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_B )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','54'])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','54'])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    r1_xboole_0 @ sk_B @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('86',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('88',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('90',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('93',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','96'])).

thf('98',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('100',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('102',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('104',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('108',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference(demod,[status(thm)],['104','105'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['97','112'])).

thf('114',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v0udYHArZU
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.14  % Solved by: fo/fo7.sh
% 0.91/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.14  % done 1798 iterations in 0.679s
% 0.91/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.14  % SZS output start Refutation
% 0.91/1.14  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.14  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.91/1.14  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.14  thf(t63_xboole_1, conjecture,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.91/1.14       ( r1_xboole_0 @ A @ C ) ))).
% 0.91/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.14    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.14        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.91/1.14          ( r1_xboole_0 @ A @ C ) ) )),
% 0.91/1.14    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.91/1.14  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(t3_xboole_0, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.91/1.14            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.14       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.14            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.91/1.14  thf('1', plain,
% 0.91/1.14      (![X13 : $i, X14 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.91/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.14  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf(t28_xboole_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.91/1.14  thf('3', plain,
% 0.91/1.14      (![X18 : $i, X19 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.91/1.14      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.91/1.14  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.91/1.14      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.14  thf(t48_xboole_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.91/1.14  thf('5', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.91/1.14           = (k3_xboole_0 @ X20 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.14  thf(d5_xboole_0, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.91/1.14       ( ![D:$i]:
% 0.91/1.14         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.14           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.91/1.14  thf('6', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X6 @ X5)
% 0.91/1.14          | ~ (r2_hidden @ X6 @ X4)
% 0.91/1.14          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.91/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.14  thf('7', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X6 @ X4)
% 0.91/1.14          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.14  thf('8', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.14          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['5', '7'])).
% 0.91/1.14  thf('9', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X0 @ sk_A)
% 0.91/1.14          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['4', '8'])).
% 0.91/1.14  thf('10', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X6 @ X5)
% 0.91/1.14          | (r2_hidden @ X6 @ X3)
% 0.91/1.14          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.91/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.14  thf('11', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.91/1.14         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['10'])).
% 0.91/1.14  thf('12', plain,
% 0.91/1.14      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.14      inference('clc', [status(thm)], ['9', '11'])).
% 0.91/1.14  thf('13', plain,
% 0.91/1.14      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.91/1.14      inference('sup-', [status(thm)], ['1', '12'])).
% 0.91/1.14  thf(d7_xboole_0, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.91/1.14       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.14  thf('14', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.91/1.14      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.14  thf('15', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) = (k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['13', '14'])).
% 0.91/1.14  thf('16', plain,
% 0.91/1.14      (![X13 : $i, X14 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.91/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.14  thf('17', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.91/1.14         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['10'])).
% 0.91/1.14  thf('18', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.91/1.14          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['16', '17'])).
% 0.91/1.14  thf('19', plain,
% 0.91/1.14      (![X13 : $i, X14 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.91/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.14  thf('20', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X6 @ X4)
% 0.91/1.14          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.14  thf('21', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.91/1.14          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.14  thf('22', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.91/1.14          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['18', '21'])).
% 0.91/1.14  thf('23', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.91/1.14      inference('simplify', [status(thm)], ['22'])).
% 0.91/1.14  thf(symmetry_r1_xboole_0, axiom,
% 0.91/1.14    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.91/1.14  thf('24', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.91/1.14  thf('25', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['23', '24'])).
% 0.91/1.14  thf('26', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.91/1.14      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.14  thf('27', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.14  thf('28', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.91/1.14           = (k3_xboole_0 @ X20 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.14  thf(t51_xboole_1, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.91/1.14       ( A ) ))).
% 0.91/1.14  thf('29', plain,
% 0.91/1.14      (![X22 : $i, X23 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.91/1.14           = (X22))),
% 0.91/1.14      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.91/1.14  thf('30', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.91/1.14           (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['28', '29'])).
% 0.91/1.14  thf(commutativity_k2_xboole_0, axiom,
% 0.91/1.14    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.91/1.14  thf('31', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.14  thf('32', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.91/1.14           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['30', '31'])).
% 0.91/1.14  thf('33', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.91/1.14           = (k3_xboole_0 @ X20 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.14  thf('34', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.91/1.14           = (k3_xboole_0 @ X20 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.14  thf('35', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.14           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['33', '34'])).
% 0.91/1.14  thf('36', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.91/1.14           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['32', '35'])).
% 0.91/1.14  thf('37', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)) @ 
% 0.91/1.14           (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['27', '36'])).
% 0.91/1.14  thf('38', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.14  thf('39', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.14  thf(t1_boole, axiom,
% 0.91/1.14    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.14  thf('40', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.91/1.14      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.14  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['39', '40'])).
% 0.91/1.14  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['37', '38', '41'])).
% 0.91/1.14  thf('43', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.14           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['33', '34'])).
% 0.91/1.14  thf('44', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.91/1.14           = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['42', '43'])).
% 0.91/1.14  thf('45', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('46', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.91/1.14      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.14  thf('47', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['45', '46'])).
% 0.91/1.14  thf('48', plain,
% 0.91/1.14      (![X22 : $i, X23 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.91/1.14           = (X22))),
% 0.91/1.14      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.91/1.14  thf('49', plain,
% 0.91/1.14      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['47', '48'])).
% 0.91/1.14  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['39', '40'])).
% 0.91/1.14  thf('51', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['49', '50'])).
% 0.91/1.14  thf('52', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i]:
% 0.91/1.14         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.91/1.14           = (k3_xboole_0 @ X20 @ X21))),
% 0.91/1.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.14  thf('53', plain,
% 0.91/1.14      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['51', '52'])).
% 0.91/1.14  thf('54', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['45', '46'])).
% 0.91/1.14  thf('55', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (k1_xboole_0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.14  thf('56', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.91/1.14      inference('simplify', [status(thm)], ['22'])).
% 0.91/1.14  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.91/1.14      inference('sup+', [status(thm)], ['55', '56'])).
% 0.91/1.14  thf('58', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.91/1.14  thf('59', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.91/1.14      inference('sup-', [status(thm)], ['57', '58'])).
% 0.91/1.14  thf('60', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.91/1.14      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.14  thf('61', plain,
% 0.91/1.14      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['59', '60'])).
% 0.91/1.14  thf('62', plain,
% 0.91/1.14      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['44', '61'])).
% 0.91/1.14  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['37', '38', '41'])).
% 0.91/1.14  thf('64', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.14      inference('demod', [status(thm)], ['62', '63'])).
% 0.91/1.14  thf('65', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['15', '64'])).
% 0.91/1.14  thf('66', plain,
% 0.91/1.14      (![X13 : $i, X14 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.91/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.14  thf('67', plain,
% 0.91/1.14      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X2 @ X3)
% 0.91/1.14          | (r2_hidden @ X2 @ X4)
% 0.91/1.14          | (r2_hidden @ X2 @ X5)
% 0.91/1.14          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.91/1.14      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.14  thf('68', plain,
% 0.91/1.14      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.14         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.91/1.14          | (r2_hidden @ X2 @ X4)
% 0.91/1.14          | ~ (r2_hidden @ X2 @ X3))),
% 0.91/1.14      inference('simplify', [status(thm)], ['67'])).
% 0.91/1.14  thf('69', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X0 @ X1)
% 0.91/1.14          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.91/1.14          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['66', '68'])).
% 0.91/1.14  thf('70', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ k1_xboole_0)
% 0.91/1.14          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.91/1.14          | (r1_xboole_0 @ sk_A @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['65', '69'])).
% 0.91/1.14  thf('71', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (k1_xboole_0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.14  thf('72', plain,
% 0.91/1.14      (![X22 : $i, X23 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.91/1.14           = (X22))),
% 0.91/1.14      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.91/1.14  thf('73', plain,
% 0.91/1.14      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_B) @ k1_xboole_0) = (sk_B))),
% 0.91/1.14      inference('sup+', [status(thm)], ['71', '72'])).
% 0.91/1.14  thf('74', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.14  thf('75', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['39', '40'])).
% 0.91/1.14  thf('76', plain, (((k3_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 0.91/1.14      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.91/1.14  thf('77', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.14           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.14      inference('sup+', [status(thm)], ['33', '34'])).
% 0.91/1.14  thf('78', plain,
% 0.91/1.14      (![X8 : $i, X10 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X8 @ X10)
% 0.91/1.14          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.91/1.14      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.14  thf('79', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.91/1.14          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['77', '78'])).
% 0.91/1.14  thf('80', plain,
% 0.91/1.14      ((((k4_xboole_0 @ sk_B @ sk_B) != (k1_xboole_0))
% 0.91/1.14        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_B)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['76', '79'])).
% 0.91/1.14  thf('81', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (k1_xboole_0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.14  thf('82', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (k1_xboole_0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.14  thf('83', plain,
% 0.91/1.14      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.91/1.14      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.91/1.14  thf('84', plain, ((r1_xboole_0 @ sk_B @ k1_xboole_0)),
% 0.91/1.14      inference('simplify', [status(thm)], ['83'])).
% 0.91/1.14  thf('85', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.91/1.14  thf('86', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_B)),
% 0.91/1.14      inference('sup-', [status(thm)], ['84', '85'])).
% 0.91/1.14  thf('87', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.91/1.14      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.14  thf('88', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['86', '87'])).
% 0.91/1.14  thf('89', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.91/1.14           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['32', '35'])).
% 0.91/1.14  thf('90', plain,
% 0.91/1.14      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.91/1.14         (k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B)))
% 0.91/1.14         = (k1_xboole_0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['88', '89'])).
% 0.91/1.14  thf('91', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['86', '87'])).
% 0.91/1.14  thf('92', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['39', '40'])).
% 0.91/1.14  thf('93', plain,
% 0.91/1.14      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.14      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.91/1.14  thf('94', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X6 @ X4)
% 0.91/1.14          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.14  thf('95', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['93', '94'])).
% 0.91/1.14  thf('96', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.91/1.14      inference('simplify', [status(thm)], ['95'])).
% 0.91/1.14  thf('97', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.91/1.14      inference('clc', [status(thm)], ['70', '96'])).
% 0.91/1.14  thf('98', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.91/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.14  thf('99', plain,
% 0.91/1.14      (![X11 : $i, X12 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.91/1.14      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.91/1.14  thf('100', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.91/1.14      inference('sup-', [status(thm)], ['98', '99'])).
% 0.91/1.14  thf('101', plain,
% 0.91/1.14      (![X8 : $i, X9 : $i]:
% 0.91/1.14         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.91/1.14      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.14  thf('102', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['100', '101'])).
% 0.91/1.14  thf('103', plain,
% 0.91/1.14      (![X22 : $i, X23 : $i]:
% 0.91/1.14         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.91/1.14           = (X22))),
% 0.91/1.14      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.91/1.14  thf('104', plain,
% 0.91/1.14      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B)) = (sk_C_1))),
% 0.91/1.14      inference('sup+', [status(thm)], ['102', '103'])).
% 0.91/1.14  thf('105', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['39', '40'])).
% 0.91/1.14  thf('106', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['104', '105'])).
% 0.91/1.14  thf('107', plain,
% 0.91/1.14      (![X13 : $i, X14 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 0.91/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.14  thf('108', plain,
% 0.91/1.14      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X6 @ X4)
% 0.91/1.14          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.91/1.14      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.14  thf('109', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.14         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.91/1.14          | ~ (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['107', '108'])).
% 0.91/1.14  thf('110', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)
% 0.91/1.14          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['106', '109'])).
% 0.91/1.14  thf('111', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['104', '105'])).
% 0.91/1.14  thf('112', plain,
% 0.91/1.14      (![X0 : $i]:
% 0.91/1.14         (~ (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_B)
% 0.91/1.14          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.91/1.14      inference('demod', [status(thm)], ['110', '111'])).
% 0.91/1.14  thf('113', plain,
% 0.91/1.14      (((r1_xboole_0 @ sk_A @ sk_C_1) | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['97', '112'])).
% 0.91/1.14  thf('114', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.91/1.14      inference('simplify', [status(thm)], ['113'])).
% 0.91/1.14  thf('115', plain, ($false), inference('demod', [status(thm)], ['0', '114'])).
% 0.91/1.14  
% 0.91/1.14  % SZS output end Refutation
% 0.91/1.14  
% 0.91/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
