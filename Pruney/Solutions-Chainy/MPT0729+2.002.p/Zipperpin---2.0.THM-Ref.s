%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mBZUt5aKjX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:41 EST 2020

% Result     : Theorem 34.54s
% Output     : Refutation 34.54s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 537 expanded)
%              Number of leaves         :   30 ( 181 expanded)
%              Depth                    :   25
%              Number of atoms          : 1294 (4160 expanded)
%              Number of equality atoms :  111 ( 413 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k4_xboole_0 @ X48 @ ( k1_tarski @ X49 ) )
        = X48 )
      | ( r2_hidden @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('1',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X50: $i] :
      ( ( k1_ordinal1 @ X50 )
      = ( k2_xboole_0 @ X50 @ ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('22',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('23',plain,(
    ! [X51: $i] :
      ( r2_hidden @ X51 @ ( k1_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('24',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ X1 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ X1 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_ordinal1 @ X0 ) ) )
      | ( r2_hidden @ sk_B @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','31'])).

thf('33',plain,(
    ! [X51: $i] :
      ( r2_hidden @ X51 @ ( k1_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('34',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r2_hidden @ X39 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ ( k1_ordinal1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_ordinal1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k2_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','45'])).

thf('47',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','51'])).

thf('53',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X41 @ X40 )
      | ~ ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','57'])).

thf('59',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('60',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('62',plain,(
    ! [X43: $i,X44: $i,X46: $i] :
      ( ( r2_hidden @ X43 @ ( k4_xboole_0 @ X44 @ ( k1_tarski @ X46 ) ) )
      | ( X43 = X46 )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('65',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X2 = X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('70',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['20','70'])).

thf('72',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('75',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('99',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('100',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('103',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k1_ordinal1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_ordinal1 @ sk_B ) @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_B ) @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['97','105'])).

thf('107',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('109',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('110',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_ordinal1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_ordinal1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k1_ordinal1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ ( k1_ordinal1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('120',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('121',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('122',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r2_hidden @ X39 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('126',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('128',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('130',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('132',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_ordinal1 @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107','108','117','118','119','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('135',plain,
    ( ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('137',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('140',plain,
    ( sk_A
    = ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    ! [X51: $i] :
      ( r2_hidden @ X51 @ ( k1_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('142',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('143',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['144','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mBZUt5aKjX
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 34.54/34.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 34.54/34.74  % Solved by: fo/fo7.sh
% 34.54/34.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 34.54/34.74  % done 27467 iterations in 34.270s
% 34.54/34.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 34.54/34.74  % SZS output start Refutation
% 34.54/34.74  thf(sk_B_type, type, sk_B: $i).
% 34.54/34.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 34.54/34.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 34.54/34.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 34.54/34.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 34.54/34.74  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 34.54/34.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 34.54/34.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 34.54/34.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 34.54/34.74  thf(sk_A_type, type, sk_A: $i).
% 34.54/34.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 34.54/34.74  thf(t65_zfmisc_1, axiom,
% 34.54/34.74    (![A:$i,B:$i]:
% 34.54/34.74     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 34.54/34.74       ( ~( r2_hidden @ B @ A ) ) ))).
% 34.54/34.74  thf('0', plain,
% 34.54/34.74      (![X48 : $i, X49 : $i]:
% 34.54/34.74         (((k4_xboole_0 @ X48 @ (k1_tarski @ X49)) = (X48))
% 34.54/34.74          | (r2_hidden @ X49 @ X48))),
% 34.54/34.74      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 34.54/34.74  thf(t12_ordinal1, conjecture,
% 34.54/34.74    (![A:$i,B:$i]:
% 34.54/34.74     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 34.54/34.74  thf(zf_stmt_0, negated_conjecture,
% 34.54/34.74    (~( ![A:$i,B:$i]:
% 34.54/34.74        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 34.54/34.74    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 34.54/34.74  thf('1', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 34.54/34.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.54/34.74  thf(t69_enumset1, axiom,
% 34.54/34.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 34.54/34.74  thf('2', plain, (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 34.54/34.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 34.54/34.74  thf(d1_ordinal1, axiom,
% 34.54/34.74    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 34.54/34.74  thf('3', plain,
% 34.54/34.74      (![X50 : $i]:
% 34.54/34.74         ((k1_ordinal1 @ X50) = (k2_xboole_0 @ X50 @ (k1_tarski @ X50)))),
% 34.54/34.74      inference('cnf', [status(esa)], [d1_ordinal1])).
% 34.54/34.74  thf('4', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['2', '3'])).
% 34.54/34.74  thf(t7_xboole_1, axiom,
% 34.54/34.74    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 34.54/34.74  thf('5', plain,
% 34.54/34.74      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 34.54/34.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 34.54/34.74  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 34.54/34.74      inference('sup+', [status(thm)], ['4', '5'])).
% 34.54/34.74  thf('7', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 34.54/34.74      inference('sup+', [status(thm)], ['1', '6'])).
% 34.54/34.74  thf('8', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['2', '3'])).
% 34.54/34.74  thf(commutativity_k2_tarski, axiom,
% 34.54/34.74    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 34.54/34.74  thf('9', plain,
% 34.54/34.74      (![X25 : $i, X26 : $i]:
% 34.54/34.74         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 34.54/34.74      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.54/34.74  thf(l51_zfmisc_1, axiom,
% 34.54/34.74    (![A:$i,B:$i]:
% 34.54/34.74     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 34.54/34.74  thf('10', plain,
% 34.54/34.74      (![X37 : $i, X38 : $i]:
% 34.54/34.74         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.54/34.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.54/34.74  thf('11', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['9', '10'])).
% 34.54/34.74  thf('12', plain,
% 34.54/34.74      (![X37 : $i, X38 : $i]:
% 34.54/34.74         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.54/34.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.54/34.74  thf('13', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['11', '12'])).
% 34.54/34.74  thf(t43_xboole_1, axiom,
% 34.54/34.74    (![A:$i,B:$i,C:$i]:
% 34.54/34.74     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 34.54/34.74       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 34.54/34.74  thf('14', plain,
% 34.54/34.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 34.54/34.74         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 34.54/34.74          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 34.54/34.74      inference('cnf', [status(esa)], [t43_xboole_1])).
% 34.54/34.74  thf('15', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.54/34.74         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 34.54/34.74          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 34.54/34.74      inference('sup-', [status(thm)], ['13', '14'])).
% 34.54/34.74  thf('16', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 34.54/34.74          | (r1_tarski @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) @ X0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['8', '15'])).
% 34.54/34.74  thf('17', plain,
% 34.54/34.74      ((r1_tarski @ (k4_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_A)) @ sk_A)),
% 34.54/34.74      inference('sup-', [status(thm)], ['7', '16'])).
% 34.54/34.74  thf('18', plain,
% 34.54/34.74      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 34.54/34.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 34.54/34.74  thf('19', plain,
% 34.54/34.74      ((r1_tarski @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_A)),
% 34.54/34.74      inference('demod', [status(thm)], ['17', '18'])).
% 34.54/34.74  thf('20', plain, (((r1_tarski @ sk_B @ sk_A) | (r2_hidden @ sk_A @ sk_B))),
% 34.54/34.74      inference('sup+', [status(thm)], ['0', '19'])).
% 34.54/34.74  thf('21', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['2', '3'])).
% 34.54/34.74  thf('22', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 34.54/34.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.54/34.74  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 34.54/34.74  thf('23', plain, (![X51 : $i]: (r2_hidden @ X51 @ (k1_ordinal1 @ X51))),
% 34.54/34.74      inference('cnf', [status(esa)], [t10_ordinal1])).
% 34.54/34.74  thf('24', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 34.54/34.74      inference('sup+', [status(thm)], ['22', '23'])).
% 34.54/34.74  thf(d5_xboole_0, axiom,
% 34.54/34.74    (![A:$i,B:$i,C:$i]:
% 34.54/34.74     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 34.54/34.74       ( ![D:$i]:
% 34.54/34.74         ( ( r2_hidden @ D @ C ) <=>
% 34.54/34.74           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 34.54/34.74  thf('25', plain,
% 34.54/34.74      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 34.54/34.74         (~ (r2_hidden @ X2 @ X3)
% 34.54/34.74          | (r2_hidden @ X2 @ X4)
% 34.54/34.74          | (r2_hidden @ X2 @ X5)
% 34.54/34.74          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 34.54/34.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 34.54/34.74  thf('26', plain,
% 34.54/34.74      (![X2 : $i, X3 : $i, X4 : $i]:
% 34.54/34.74         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 34.54/34.74          | (r2_hidden @ X2 @ X4)
% 34.54/34.74          | ~ (r2_hidden @ X2 @ X3))),
% 34.54/34.74      inference('simplify', [status(thm)], ['25'])).
% 34.54/34.74  thf('27', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((r2_hidden @ sk_B @ X0)
% 34.54/34.74          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0)))),
% 34.54/34.74      inference('sup-', [status(thm)], ['24', '26'])).
% 34.54/34.74  thf('28', plain,
% 34.54/34.74      (![X2 : $i, X3 : $i, X4 : $i]:
% 34.54/34.74         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 34.54/34.74          | (r2_hidden @ X2 @ X4)
% 34.54/34.74          | ~ (r2_hidden @ X2 @ X3))),
% 34.54/34.74      inference('simplify', [status(thm)], ['25'])).
% 34.54/34.74  thf('29', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         ((r2_hidden @ sk_B @ X0)
% 34.54/34.74          | (r2_hidden @ sk_B @ X1)
% 34.54/34.74          | (r2_hidden @ sk_B @ 
% 34.54/34.74             (k4_xboole_0 @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0) @ X1)))),
% 34.54/34.74      inference('sup-', [status(thm)], ['27', '28'])).
% 34.54/34.74  thf(t41_xboole_1, axiom,
% 34.54/34.74    (![A:$i,B:$i,C:$i]:
% 34.54/34.74     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 34.54/34.74       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 34.54/34.74  thf('30', plain,
% 34.54/34.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 34.54/34.74           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 34.54/34.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 34.54/34.74  thf('31', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         ((r2_hidden @ sk_B @ X0)
% 34.54/34.74          | (r2_hidden @ sk_B @ X1)
% 34.54/34.74          | (r2_hidden @ sk_B @ 
% 34.54/34.74             (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k2_xboole_0 @ X0 @ X1))))),
% 34.54/34.74      inference('demod', [status(thm)], ['29', '30'])).
% 34.54/34.74  thf('32', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((r2_hidden @ sk_B @ 
% 34.54/34.74           (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_ordinal1 @ X0)))
% 34.54/34.74          | (r2_hidden @ sk_B @ (k2_tarski @ X0 @ X0))
% 34.54/34.74          | (r2_hidden @ sk_B @ X0))),
% 34.54/34.74      inference('sup+', [status(thm)], ['21', '31'])).
% 34.54/34.74  thf('33', plain, (![X51 : $i]: (r2_hidden @ X51 @ (k1_ordinal1 @ X51))),
% 34.54/34.74      inference('cnf', [status(esa)], [t10_ordinal1])).
% 34.54/34.74  thf('34', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 34.54/34.74      inference('sup+', [status(thm)], ['22', '23'])).
% 34.54/34.74  thf(t38_zfmisc_1, axiom,
% 34.54/34.74    (![A:$i,B:$i,C:$i]:
% 34.54/34.74     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 34.54/34.74       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 34.54/34.74  thf('35', plain,
% 34.54/34.74      (![X39 : $i, X41 : $i, X42 : $i]:
% 34.54/34.74         ((r1_tarski @ (k2_tarski @ X39 @ X41) @ X42)
% 34.54/34.74          | ~ (r2_hidden @ X41 @ X42)
% 34.54/34.74          | ~ (r2_hidden @ X39 @ X42))),
% 34.54/34.74      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 34.54/34.74  thf('36', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         (~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))
% 34.54/34.74          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ (k1_ordinal1 @ sk_A)))),
% 34.54/34.74      inference('sup-', [status(thm)], ['34', '35'])).
% 34.54/34.74  thf('37', plain,
% 34.54/34.74      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_ordinal1 @ sk_A))),
% 34.54/34.74      inference('sup-', [status(thm)], ['33', '36'])).
% 34.54/34.74  thf(l32_xboole_1, axiom,
% 34.54/34.74    (![A:$i,B:$i]:
% 34.54/34.74     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 34.54/34.74  thf('38', plain,
% 34.54/34.74      (![X11 : $i, X13 : $i]:
% 34.54/34.74         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 34.54/34.74          | ~ (r1_tarski @ X11 @ X13))),
% 34.54/34.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 34.54/34.74  thf('39', plain,
% 34.54/34.74      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_ordinal1 @ sk_A))
% 34.54/34.74         = (k1_xboole_0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['37', '38'])).
% 34.54/34.74  thf(t39_xboole_1, axiom,
% 34.54/34.74    (![A:$i,B:$i]:
% 34.54/34.74     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 34.54/34.74  thf('40', plain,
% 34.54/34.74      (![X15 : $i, X16 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 34.54/34.74           = (k2_xboole_0 @ X15 @ X16))),
% 34.54/34.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 34.54/34.74  thf('41', plain,
% 34.54/34.74      (((k2_xboole_0 @ (k1_ordinal1 @ sk_A) @ k1_xboole_0)
% 34.54/34.74         = (k2_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k2_tarski @ sk_A @ sk_B)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['39', '40'])).
% 34.54/34.74  thf('42', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['11', '12'])).
% 34.54/34.74  thf('43', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['11', '12'])).
% 34.54/34.74  thf(t1_boole, axiom,
% 34.54/34.74    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 34.54/34.74  thf('44', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 34.54/34.74      inference('cnf', [status(esa)], [t1_boole])).
% 34.54/34.74  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 34.54/34.74      inference('sup+', [status(thm)], ['43', '44'])).
% 34.54/34.74  thf('46', plain,
% 34.54/34.74      (((k1_ordinal1 @ sk_A)
% 34.54/34.74         = (k2_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k2_tarski @ sk_A @ sk_B)))),
% 34.54/34.74      inference('demod', [status(thm)], ['41', '42', '45'])).
% 34.54/34.74  thf('47', plain,
% 34.54/34.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 34.54/34.74           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 34.54/34.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 34.54/34.74  thf('48', plain,
% 34.54/34.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 34.54/34.74         (~ (r2_hidden @ X6 @ X5)
% 34.54/34.74          | ~ (r2_hidden @ X6 @ X4)
% 34.54/34.74          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 34.54/34.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 34.54/34.74  thf('49', plain,
% 34.54/34.74      (![X3 : $i, X4 : $i, X6 : $i]:
% 34.54/34.74         (~ (r2_hidden @ X6 @ X4)
% 34.54/34.74          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 34.54/34.74      inference('simplify', [status(thm)], ['48'])).
% 34.54/34.74  thf('50', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.54/34.74         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 34.54/34.74          | ~ (r2_hidden @ X3 @ X0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['47', '49'])).
% 34.54/34.74  thf('51', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ (k1_ordinal1 @ sk_A)))
% 34.54/34.74          | ~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ sk_B)))),
% 34.54/34.74      inference('sup-', [status(thm)], ['46', '50'])).
% 34.54/34.74  thf('52', plain,
% 34.54/34.74      (((r2_hidden @ sk_B @ sk_A)
% 34.54/34.74        | (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 34.54/34.74        | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))),
% 34.54/34.74      inference('sup-', [status(thm)], ['32', '51'])).
% 34.54/34.74  thf('53', plain,
% 34.54/34.74      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 34.54/34.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 34.54/34.74  thf(d10_xboole_0, axiom,
% 34.54/34.74    (![A:$i,B:$i]:
% 34.54/34.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 34.54/34.74  thf('54', plain,
% 34.54/34.74      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 34.54/34.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 34.54/34.74  thf('55', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 34.54/34.74      inference('simplify', [status(thm)], ['54'])).
% 34.54/34.74  thf('56', plain,
% 34.54/34.74      (![X39 : $i, X40 : $i, X41 : $i]:
% 34.54/34.74         ((r2_hidden @ X41 @ X40)
% 34.54/34.74          | ~ (r1_tarski @ (k2_tarski @ X39 @ X41) @ X40))),
% 34.54/34.74      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 34.54/34.74  thf('57', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['55', '56'])).
% 34.54/34.74  thf('58', plain,
% 34.54/34.74      (((r2_hidden @ sk_B @ sk_A) | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 34.54/34.74      inference('demod', [status(thm)], ['52', '53', '57'])).
% 34.54/34.74  thf('59', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 34.54/34.74      inference('simplify', [status(thm)], ['54'])).
% 34.54/34.74  thf('60', plain,
% 34.54/34.74      (![X39 : $i, X40 : $i, X41 : $i]:
% 34.54/34.74         ((r2_hidden @ X39 @ X40)
% 34.54/34.74          | ~ (r1_tarski @ (k2_tarski @ X39 @ X41) @ X40))),
% 34.54/34.74      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 34.54/34.74  thf('61', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['59', '60'])).
% 34.54/34.74  thf(t64_zfmisc_1, axiom,
% 34.54/34.74    (![A:$i,B:$i,C:$i]:
% 34.54/34.74     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 34.54/34.74       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 34.54/34.74  thf('62', plain,
% 34.54/34.74      (![X43 : $i, X44 : $i, X46 : $i]:
% 34.54/34.74         ((r2_hidden @ X43 @ (k4_xboole_0 @ X44 @ (k1_tarski @ X46)))
% 34.54/34.74          | ((X43) = (X46))
% 34.54/34.74          | ~ (r2_hidden @ X43 @ X44))),
% 34.54/34.74      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 34.54/34.74  thf('63', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.54/34.74         (((X1) = (X2))
% 34.54/34.74          | (r2_hidden @ X1 @ 
% 34.54/34.74             (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))))),
% 34.54/34.74      inference('sup-', [status(thm)], ['61', '62'])).
% 34.54/34.74  thf('64', plain,
% 34.54/34.74      (![X3 : $i, X4 : $i, X6 : $i]:
% 34.54/34.74         (~ (r2_hidden @ X6 @ X4)
% 34.54/34.74          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 34.54/34.74      inference('simplify', [status(thm)], ['48'])).
% 34.54/34.74  thf('65', plain,
% 34.54/34.74      (![X0 : $i, X2 : $i]:
% 34.54/34.74         (((X2) = (X0)) | ~ (r2_hidden @ X2 @ (k1_tarski @ X0)))),
% 34.54/34.74      inference('sup-', [status(thm)], ['63', '64'])).
% 34.54/34.74  thf('66', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 34.54/34.74      inference('sup-', [status(thm)], ['58', '65'])).
% 34.54/34.74  thf('67', plain, (((sk_A) != (sk_B))),
% 34.54/34.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.54/34.74  thf('68', plain, ((r2_hidden @ sk_B @ sk_A)),
% 34.54/34.74      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 34.54/34.74  thf(antisymmetry_r2_hidden, axiom,
% 34.54/34.74    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 34.54/34.74  thf('69', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 34.54/34.74      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 34.54/34.74  thf('70', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 34.54/34.74      inference('sup-', [status(thm)], ['68', '69'])).
% 34.54/34.74  thf('71', plain, ((r1_tarski @ sk_B @ sk_A)),
% 34.54/34.74      inference('clc', [status(thm)], ['20', '70'])).
% 34.54/34.74  thf('72', plain,
% 34.54/34.74      (![X11 : $i, X13 : $i]:
% 34.54/34.74         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 34.54/34.74          | ~ (r1_tarski @ X11 @ X13))),
% 34.54/34.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 34.54/34.74  thf('73', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['71', '72'])).
% 34.54/34.74  thf('74', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 34.54/34.74      inference('simplify', [status(thm)], ['54'])).
% 34.54/34.74  thf('75', plain,
% 34.54/34.74      (![X11 : $i, X13 : $i]:
% 34.54/34.74         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 34.54/34.74          | ~ (r1_tarski @ X11 @ X13))),
% 34.54/34.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 34.54/34.74  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['74', '75'])).
% 34.54/34.74  thf('77', plain,
% 34.54/34.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 34.54/34.74           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 34.54/34.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 34.54/34.74  thf('78', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         ((k1_xboole_0)
% 34.54/34.74           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 34.54/34.74      inference('sup+', [status(thm)], ['76', '77'])).
% 34.54/34.74  thf('79', plain,
% 34.54/34.74      (![X15 : $i, X16 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 34.54/34.74           = (k2_xboole_0 @ X15 @ X16))),
% 34.54/34.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 34.54/34.74  thf('80', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 34.54/34.74      inference('demod', [status(thm)], ['78', '79'])).
% 34.54/34.74  thf('81', plain,
% 34.54/34.74      (![X15 : $i, X16 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 34.54/34.74           = (k2_xboole_0 @ X15 @ X16))),
% 34.54/34.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 34.54/34.74  thf('82', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 34.54/34.74           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 34.54/34.74      inference('sup+', [status(thm)], ['80', '81'])).
% 34.54/34.74  thf('83', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 34.54/34.74      inference('cnf', [status(esa)], [t1_boole])).
% 34.54/34.74  thf('84', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X1 @ X0)
% 34.54/34.74           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 34.54/34.74      inference('demod', [status(thm)], ['82', '83'])).
% 34.54/34.74  thf('85', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['11', '12'])).
% 34.54/34.74  thf('86', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X1 @ X0)
% 34.54/34.74           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 34.54/34.74      inference('demod', [status(thm)], ['84', '85'])).
% 34.54/34.74  thf('87', plain,
% 34.54/34.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 34.54/34.74           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 34.54/34.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 34.54/34.74  thf('88', plain,
% 34.54/34.74      (![X15 : $i, X16 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 34.54/34.74           = (k2_xboole_0 @ X15 @ X16))),
% 34.54/34.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 34.54/34.74  thf('89', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 34.54/34.74           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['87', '88'])).
% 34.54/34.74  thf('90', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 34.54/34.74           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 34.54/34.74           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['86', '89'])).
% 34.54/34.74  thf('91', plain,
% 34.54/34.74      (![X15 : $i, X16 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 34.54/34.74           = (k2_xboole_0 @ X15 @ X16))),
% 34.54/34.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 34.54/34.74  thf('92', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 34.54/34.74           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0)))),
% 34.54/34.74      inference('demod', [status(thm)], ['90', '91'])).
% 34.54/34.74  thf('93', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B)
% 34.54/34.74           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ sk_A) @ k1_xboole_0))),
% 34.54/34.74      inference('sup+', [status(thm)], ['73', '92'])).
% 34.54/34.74  thf('94', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['11', '12'])).
% 34.54/34.74  thf('95', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['11', '12'])).
% 34.54/34.74  thf('96', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 34.54/34.74      inference('sup+', [status(thm)], ['43', '44'])).
% 34.54/34.74  thf('97', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))
% 34.54/34.74           = (k2_xboole_0 @ X0 @ sk_A))),
% 34.54/34.74      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 34.54/34.74  thf('98', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['2', '3'])).
% 34.54/34.74  thf('99', plain,
% 34.54/34.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 34.54/34.74           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 34.54/34.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 34.54/34.74  thf('100', plain,
% 34.54/34.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 34.54/34.74           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 34.54/34.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 34.54/34.74  thf('101', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 34.54/34.74           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['99', '100'])).
% 34.54/34.74  thf('102', plain,
% 34.54/34.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 34.54/34.74           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 34.54/34.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 34.54/34.74  thf('103', plain,
% 34.54/34.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 34.54/34.74           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 34.54/34.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 34.54/34.74  thf('104', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 34.54/34.74           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 34.54/34.74      inference('demod', [status(thm)], ['101', '102', '103'])).
% 34.54/34.74  thf('105', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k1_ordinal1 @ X0) @ X1))
% 34.54/34.74           = (k4_xboole_0 @ X2 @ 
% 34.54/34.74              (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))))),
% 34.54/34.74      inference('sup+', [status(thm)], ['98', '104'])).
% 34.54/34.74  thf('106', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k1_ordinal1 @ sk_B) @ sk_A))
% 34.54/34.74           = (k4_xboole_0 @ X0 @ 
% 34.54/34.74              (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_B) @ sk_A)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['97', '105'])).
% 34.54/34.74  thf('107', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 34.54/34.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.54/34.74  thf('108', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['11', '12'])).
% 34.54/34.74  thf('109', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 34.54/34.74      inference('sup+', [status(thm)], ['4', '5'])).
% 34.54/34.74  thf('110', plain,
% 34.54/34.74      (![X11 : $i, X13 : $i]:
% 34.54/34.74         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 34.54/34.74          | ~ (r1_tarski @ X11 @ X13))),
% 34.54/34.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 34.54/34.74  thf('111', plain,
% 34.54/34.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k1_ordinal1 @ X0)) = (k1_xboole_0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['109', '110'])).
% 34.54/34.74  thf('112', plain,
% 34.54/34.74      (![X15 : $i, X16 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 34.54/34.74           = (k2_xboole_0 @ X15 @ X16))),
% 34.54/34.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 34.54/34.74  thf('113', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ (k1_ordinal1 @ X0) @ k1_xboole_0)
% 34.54/34.74           = (k2_xboole_0 @ (k1_ordinal1 @ X0) @ X0))),
% 34.54/34.74      inference('sup+', [status(thm)], ['111', '112'])).
% 34.54/34.74  thf('114', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 34.54/34.74      inference('cnf', [status(esa)], [t1_boole])).
% 34.54/34.74  thf('115', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ (k1_ordinal1 @ X0) @ X0))),
% 34.54/34.74      inference('demod', [status(thm)], ['113', '114'])).
% 34.54/34.74  thf('116', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['11', '12'])).
% 34.54/34.74  thf('117', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k1_ordinal1 @ X0)))),
% 34.54/34.74      inference('demod', [status(thm)], ['115', '116'])).
% 34.54/34.74  thf('118', plain,
% 34.54/34.74      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 34.54/34.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 34.54/34.74  thf('119', plain,
% 34.54/34.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 34.54/34.74      inference('sup+', [status(thm)], ['11', '12'])).
% 34.54/34.74  thf('120', plain, ((r2_hidden @ sk_B @ sk_A)),
% 34.54/34.74      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 34.54/34.74  thf('121', plain, ((r2_hidden @ sk_B @ sk_A)),
% 34.54/34.74      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 34.54/34.74  thf('122', plain,
% 34.54/34.74      (![X39 : $i, X41 : $i, X42 : $i]:
% 34.54/34.74         ((r1_tarski @ (k2_tarski @ X39 @ X41) @ X42)
% 34.54/34.74          | ~ (r2_hidden @ X41 @ X42)
% 34.54/34.74          | ~ (r2_hidden @ X39 @ X42))),
% 34.54/34.74      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 34.54/34.74  thf('123', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         (~ (r2_hidden @ X0 @ sk_A)
% 34.54/34.74          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_A))),
% 34.54/34.74      inference('sup-', [status(thm)], ['121', '122'])).
% 34.54/34.74  thf('124', plain, ((r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ sk_A)),
% 34.54/34.74      inference('sup-', [status(thm)], ['120', '123'])).
% 34.54/34.74  thf('125', plain,
% 34.54/34.74      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 34.54/34.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 34.54/34.74  thf('126', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 34.54/34.74      inference('demod', [status(thm)], ['124', '125'])).
% 34.54/34.74  thf('127', plain,
% 34.54/34.74      (![X11 : $i, X13 : $i]:
% 34.54/34.74         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 34.54/34.74          | ~ (r1_tarski @ X11 @ X13))),
% 34.54/34.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 34.54/34.74  thf('128', plain,
% 34.54/34.74      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['126', '127'])).
% 34.54/34.74  thf('129', plain,
% 34.54/34.74      (![X15 : $i, X16 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 34.54/34.74           = (k2_xboole_0 @ X15 @ X16))),
% 34.54/34.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 34.54/34.74  thf('130', plain,
% 34.54/34.74      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 34.54/34.74         = (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['128', '129'])).
% 34.54/34.74  thf('131', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 34.54/34.74      inference('cnf', [status(esa)], [t1_boole])).
% 34.54/34.74  thf('132', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 34.54/34.74      inference('demod', [status(thm)], ['130', '131'])).
% 34.54/34.74  thf('133', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k4_xboole_0 @ X0 @ (k1_ordinal1 @ sk_A)) = (k4_xboole_0 @ X0 @ sk_A))),
% 34.54/34.74      inference('demod', [status(thm)],
% 34.54/34.74                ['106', '107', '108', '117', '118', '119', '132'])).
% 34.54/34.74  thf('134', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 34.54/34.74      inference('sup-', [status(thm)], ['74', '75'])).
% 34.54/34.74  thf('135', plain,
% 34.54/34.74      (((k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ sk_A) = (k1_xboole_0))),
% 34.54/34.74      inference('sup+', [status(thm)], ['133', '134'])).
% 34.54/34.74  thf('136', plain,
% 34.54/34.74      (![X15 : $i, X16 : $i]:
% 34.54/34.74         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 34.54/34.74           = (k2_xboole_0 @ X15 @ X16))),
% 34.54/34.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 34.54/34.74  thf('137', plain,
% 34.54/34.74      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 34.54/34.74         = (k2_xboole_0 @ sk_A @ (k1_ordinal1 @ sk_A)))),
% 34.54/34.74      inference('sup+', [status(thm)], ['135', '136'])).
% 34.54/34.74  thf('138', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 34.54/34.74      inference('cnf', [status(esa)], [t1_boole])).
% 34.54/34.74  thf('139', plain,
% 34.54/34.74      (![X0 : $i]:
% 34.54/34.74         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k1_ordinal1 @ X0)))),
% 34.54/34.74      inference('demod', [status(thm)], ['115', '116'])).
% 34.54/34.74  thf('140', plain, (((sk_A) = (k1_ordinal1 @ sk_A))),
% 34.54/34.74      inference('demod', [status(thm)], ['137', '138', '139'])).
% 34.54/34.74  thf('141', plain, (![X51 : $i]: (r2_hidden @ X51 @ (k1_ordinal1 @ X51))),
% 34.54/34.74      inference('cnf', [status(esa)], [t10_ordinal1])).
% 34.54/34.74  thf(t7_ordinal1, axiom,
% 34.54/34.74    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 34.54/34.74  thf('142', plain,
% 34.54/34.74      (![X52 : $i, X53 : $i]:
% 34.54/34.74         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 34.54/34.74      inference('cnf', [status(esa)], [t7_ordinal1])).
% 34.54/34.74  thf('143', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 34.54/34.74      inference('sup-', [status(thm)], ['141', '142'])).
% 34.54/34.74  thf('144', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 34.54/34.74      inference('sup-', [status(thm)], ['140', '143'])).
% 34.54/34.74  thf('145', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 34.54/34.74      inference('simplify', [status(thm)], ['54'])).
% 34.54/34.74  thf('146', plain, ($false), inference('demod', [status(thm)], ['144', '145'])).
% 34.54/34.74  
% 34.54/34.74  % SZS output end Refutation
% 34.54/34.74  
% 34.54/34.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
