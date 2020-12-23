%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.heE5ys2Iwu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:16 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 127 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  720 (1048 expanded)
%              Number of equality atoms :   63 (  93 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t48_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('40',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','51'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('53',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','54'])).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['13','18','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','68'])).

thf('70',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.heE5ys2Iwu
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:04:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.74/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.93  % Solved by: fo/fo7.sh
% 0.74/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.93  % done 1433 iterations in 0.484s
% 0.74/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.93  % SZS output start Refutation
% 0.74/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.74/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.74/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.74/0.93  thf(t48_xboole_1, conjecture,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.74/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.93    (~( ![A:$i,B:$i]:
% 0.74/0.93        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 0.74/0.93          ( k3_xboole_0 @ A @ B ) ) )),
% 0.74/0.93    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 0.74/0.93  thf('0', plain,
% 0.74/0.93      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.74/0.93         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t47_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.74/0.93  thf('1', plain,
% 0.74/0.93      (![X23 : $i, X24 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.74/0.93           = (k4_xboole_0 @ X23 @ X24))),
% 0.74/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.74/0.93  thf(t39_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.74/0.93  thf('2', plain,
% 0.74/0.93      (![X18 : $i, X19 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.74/0.93           = (k2_xboole_0 @ X18 @ X19))),
% 0.74/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.93  thf('3', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.74/0.93           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.74/0.93      inference('sup+', [status(thm)], ['1', '2'])).
% 0.74/0.93  thf(commutativity_k2_xboole_0, axiom,
% 0.74/0.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.74/0.93  thf('4', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.74/0.93  thf(t22_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.74/0.93  thf('5', plain,
% 0.74/0.93      (![X16 : $i, X17 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)) = (X16))),
% 0.74/0.93      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.74/0.93  thf('6', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.74/0.93           = (X1))),
% 0.74/0.93      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.74/0.93  thf(t40_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.74/0.93  thf('7', plain,
% 0.74/0.93      (![X21 : $i, X22 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22)
% 0.74/0.93           = (k4_xboole_0 @ X21 @ X22))),
% 0.74/0.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.74/0.93  thf('8', plain,
% 0.74/0.93      (![X18 : $i, X19 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.74/0.93           = (k2_xboole_0 @ X18 @ X19))),
% 0.74/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.93  thf('9', plain,
% 0.74/0.93      (![X21 : $i, X22 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22)
% 0.74/0.93           = (k4_xboole_0 @ X21 @ X22))),
% 0.74/0.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.74/0.93  thf('10', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.74/0.93           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['8', '9'])).
% 0.74/0.93  thf('11', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.74/0.93           (k4_xboole_0 @ X1 @ X0))
% 0.74/0.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['7', '10'])).
% 0.74/0.93  thf('12', plain,
% 0.74/0.93      (![X21 : $i, X22 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22)
% 0.74/0.93           = (k4_xboole_0 @ X21 @ X22))),
% 0.74/0.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.74/0.93  thf('13', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.74/0.93           (k4_xboole_0 @ X1 @ X0))
% 0.74/0.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.74/0.93      inference('demod', [status(thm)], ['11', '12'])).
% 0.74/0.93  thf('14', plain,
% 0.74/0.93      (![X21 : $i, X22 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22)
% 0.74/0.93           = (k4_xboole_0 @ X21 @ X22))),
% 0.74/0.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.74/0.93  thf('15', plain,
% 0.74/0.93      (![X18 : $i, X19 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.74/0.93           = (k2_xboole_0 @ X18 @ X19))),
% 0.74/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.93  thf('16', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.74/0.93           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['14', '15'])).
% 0.74/0.93  thf('17', plain,
% 0.74/0.93      (![X18 : $i, X19 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.74/0.93           = (k2_xboole_0 @ X18 @ X19))),
% 0.74/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.93  thf('18', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.74/0.93           = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('sup+', [status(thm)], ['16', '17'])).
% 0.74/0.93  thf(t3_xboole_0, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.74/0.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.74/0.93            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.74/0.93  thf('19', plain,
% 0.74/0.93      (![X8 : $i, X9 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.74/0.93  thf('20', plain,
% 0.74/0.93      (![X8 : $i, X9 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.74/0.93  thf(d5_xboole_0, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.74/0.93       ( ![D:$i]:
% 0.74/0.93         ( ( r2_hidden @ D @ C ) <=>
% 0.74/0.93           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.74/0.93  thf('21', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X6 @ X5)
% 0.74/0.93          | ~ (r2_hidden @ X6 @ X4)
% 0.74/0.93          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.74/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.74/0.93  thf('22', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X6 @ X4)
% 0.74/0.93          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.74/0.93      inference('simplify', [status(thm)], ['21'])).
% 0.74/0.93  thf('23', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.74/0.93          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['20', '22'])).
% 0.74/0.93  thf('24', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.74/0.93          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['19', '23'])).
% 0.74/0.93  thf('25', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.74/0.93      inference('simplify', [status(thm)], ['24'])).
% 0.74/0.93  thf('26', plain,
% 0.74/0.93      (![X8 : $i, X9 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.74/0.93  thf('27', plain,
% 0.74/0.93      (![X8 : $i, X9 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.74/0.93  thf('28', plain,
% 0.74/0.93      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X10 @ X8)
% 0.74/0.93          | ~ (r2_hidden @ X10 @ X11)
% 0.74/0.93          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.74/0.93  thf('29', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X1 @ X0)
% 0.74/0.93          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.74/0.93          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.74/0.93      inference('sup-', [status(thm)], ['27', '28'])).
% 0.74/0.93  thf('30', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X0 @ X1)
% 0.74/0.93          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.74/0.93          | (r1_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('sup-', [status(thm)], ['26', '29'])).
% 0.74/0.93  thf('31', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('simplify', [status(thm)], ['30'])).
% 0.74/0.93  thf('32', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['25', '31'])).
% 0.74/0.93  thf('33', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.74/0.93         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.74/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.74/0.93          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.74/0.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.74/0.93  thf(t3_boole, axiom,
% 0.74/0.93    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.74/0.93  thf('34', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.93  thf('35', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X6 @ X4)
% 0.74/0.93          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.74/0.93      inference('simplify', [status(thm)], ['21'])).
% 0.74/0.93  thf('36', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['34', '35'])).
% 0.74/0.93  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.74/0.93      inference('condensation', [status(thm)], ['36'])).
% 0.74/0.93  thf('38', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.74/0.93          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['33', '37'])).
% 0.74/0.93  thf('39', plain,
% 0.74/0.93      (![X21 : $i, X22 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22)
% 0.74/0.93           = (k4_xboole_0 @ X21 @ X22))),
% 0.74/0.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.74/0.93  thf('40', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.93  thf('41', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['39', '40'])).
% 0.74/0.93  thf('42', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.93  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['41', '42'])).
% 0.74/0.93  thf('44', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.74/0.93  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['43', '44'])).
% 0.74/0.93  thf('46', plain,
% 0.74/0.93      (![X16 : $i, X17 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)) = (X16))),
% 0.74/0.93      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.74/0.93  thf('47', plain,
% 0.74/0.93      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['45', '46'])).
% 0.74/0.93  thf('48', plain,
% 0.74/0.93      (![X23 : $i, X24 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.74/0.93           = (k4_xboole_0 @ X23 @ X24))),
% 0.74/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.74/0.93  thf('49', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.74/0.93           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['47', '48'])).
% 0.74/0.93  thf('50', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.93  thf('51', plain,
% 0.74/0.93      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.74/0.93      inference('demod', [status(thm)], ['49', '50'])).
% 0.74/0.93  thf('52', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.74/0.93          | ((X1) = (k1_xboole_0)))),
% 0.74/0.93      inference('demod', [status(thm)], ['38', '51'])).
% 0.74/0.93  thf(t4_xboole_0, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.74/0.93            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.74/0.93  thf('53', plain,
% 0.74/0.93      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 0.74/0.93          | ~ (r1_xboole_0 @ X12 @ X15))),
% 0.74/0.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.74/0.93  thf('54', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['52', '53'])).
% 0.74/0.93  thf('55', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['32', '54'])).
% 0.74/0.93  thf('56', plain,
% 0.74/0.93      (![X23 : $i, X24 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.74/0.93           = (k4_xboole_0 @ X23 @ X24))),
% 0.74/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.74/0.93  thf('57', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.74/0.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['55', '56'])).
% 0.74/0.93  thf('58', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.93  thf('59', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.74/0.93      inference('demod', [status(thm)], ['57', '58'])).
% 0.74/0.93  thf('60', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.74/0.93           = (X0))),
% 0.74/0.93      inference('demod', [status(thm)], ['13', '18', '59'])).
% 0.74/0.93  thf('61', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X0 @ 
% 0.74/0.93           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))
% 0.74/0.93           = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('sup+', [status(thm)], ['6', '60'])).
% 0.74/0.93  thf('62', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.74/0.93           = (X1))),
% 0.74/0.93      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.74/0.93  thf('63', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.74/0.93  thf('64', plain,
% 0.74/0.93      (![X21 : $i, X22 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22)
% 0.74/0.93           = (k4_xboole_0 @ X21 @ X22))),
% 0.74/0.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.74/0.93  thf('65', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.74/0.93           = (k4_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('sup+', [status(thm)], ['63', '64'])).
% 0.74/0.93  thf('66', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.74/0.93           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['62', '65'])).
% 0.74/0.93  thf('67', plain,
% 0.74/0.93      (![X23 : $i, X24 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.74/0.93           = (k4_xboole_0 @ X23 @ X24))),
% 0.74/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.74/0.93  thf('68', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X0 @ X1)
% 0.74/0.93           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.74/0.93      inference('demod', [status(thm)], ['66', '67'])).
% 0.74/0.93  thf('69', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.74/0.93           = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('demod', [status(thm)], ['61', '68'])).
% 0.74/0.93  thf('70', plain,
% 0.74/0.93      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.74/0.93      inference('demod', [status(thm)], ['0', '69'])).
% 0.74/0.93  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.74/0.93  
% 0.74/0.93  % SZS output end Refutation
% 0.74/0.93  
% 0.79/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
