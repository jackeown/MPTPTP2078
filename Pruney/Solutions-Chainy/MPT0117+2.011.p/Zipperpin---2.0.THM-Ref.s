%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.47dw6Rcxx6

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:48 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 235 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :  755 (1666 expanded)
%              Number of equality atoms :   73 ( 180 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_B_1 )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k5_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('9',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['15','16','19'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_xboole_0 @ X34 @ X35 )
      = ( k5_xboole_0 @ X34 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) @ sk_C_1 )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) @ sk_C_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['22','23','24','29'])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['6','30'])).

thf('32',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_xboole_0 @ X34 @ X35 )
      = ( k5_xboole_0 @ X34 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_C_1
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('48',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k5_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('55',plain,(
    r1_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_xboole_0 @ X34 @ X35 )
      = ( k5_xboole_0 @ X34 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('64',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('68',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['52','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('73',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('75',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','77'])).

thf(t97_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
        & ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ) )).

thf('79',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ X31 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X32 @ X31 ) @ X33 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t97_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B_1 )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['46','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('83',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.47dw6Rcxx6
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:14:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.06/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.26  % Solved by: fo/fo7.sh
% 1.06/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.26  % done 994 iterations in 0.785s
% 1.06/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.26  % SZS output start Refutation
% 1.06/1.26  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.06/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.26  thf(sk_B_type, type, sk_B: $i > $i).
% 1.06/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.26  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.06/1.26  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.26  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.06/1.26  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.06/1.26  thf(t110_xboole_1, conjecture,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.06/1.26       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.06/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.26    (~( ![A:$i,B:$i,C:$i]:
% 1.06/1.26        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.06/1.26          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 1.06/1.26    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 1.06/1.26  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(t36_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.06/1.26  thf('1', plain,
% 1.06/1.26      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 1.06/1.26      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.26  thf('2', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(t28_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.06/1.26  thf('3', plain,
% 1.06/1.26      (![X17 : $i, X18 : $i]:
% 1.06/1.26         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 1.06/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.06/1.26  thf('4', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 1.06/1.26      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.26  thf(t93_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( k2_xboole_0 @ A @ B ) =
% 1.06/1.26       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.06/1.26  thf('5', plain,
% 1.06/1.26      (![X29 : $i, X30 : $i]:
% 1.06/1.26         ((k2_xboole_0 @ X29 @ X30)
% 1.06/1.26           = (k2_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 1.06/1.26              (k3_xboole_0 @ X29 @ X30)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t93_xboole_1])).
% 1.06/1.26  thf('6', plain,
% 1.06/1.26      (((k2_xboole_0 @ sk_C_1 @ sk_B_1)
% 1.06/1.26         = (k2_xboole_0 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1) @ sk_C_1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['4', '5'])).
% 1.06/1.26  thf('7', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 1.06/1.26      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.26  thf(l97_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.06/1.26  thf('8', plain,
% 1.06/1.26      (![X7 : $i, X8 : $i]:
% 1.06/1.26         (r1_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k5_xboole_0 @ X7 @ X8))),
% 1.06/1.26      inference('cnf', [status(esa)], [l97_xboole_1])).
% 1.06/1.26  thf('9', plain, ((r1_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['7', '8'])).
% 1.06/1.26  thf(t7_xboole_0, axiom,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.06/1.26          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.06/1.26  thf('10', plain,
% 1.06/1.26      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.06/1.26      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.06/1.26  thf(t4_xboole_0, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.06/1.26            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.06/1.26       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.06/1.26            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.06/1.26  thf('11', plain,
% 1.06/1.26      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.06/1.26         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 1.06/1.26          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.06/1.26      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.06/1.26  thf('12', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['10', '11'])).
% 1.06/1.26  thf('13', plain,
% 1.06/1.26      (((k3_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1))
% 1.06/1.26         = (k1_xboole_0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['9', '12'])).
% 1.06/1.26  thf(t100_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.06/1.26  thf('14', plain,
% 1.06/1.26      (![X9 : $i, X10 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X9 @ X10)
% 1.06/1.26           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.26  thf('15', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1))
% 1.06/1.26         = (k5_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['13', '14'])).
% 1.06/1.26  thf(commutativity_k5_xboole_0, axiom,
% 1.06/1.26    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.06/1.26  thf('16', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.26  thf('17', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.26  thf(t5_boole, axiom,
% 1.06/1.26    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.26  thf('18', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 1.06/1.26      inference('cnf', [status(esa)], [t5_boole])).
% 1.06/1.26  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.26  thf('20', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1)) = (sk_C_1))),
% 1.06/1.26      inference('demod', [status(thm)], ['15', '16', '19'])).
% 1.06/1.26  thf(t98_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.06/1.26  thf('21', plain,
% 1.06/1.26      (![X34 : $i, X35 : $i]:
% 1.06/1.26         ((k2_xboole_0 @ X34 @ X35)
% 1.06/1.26           = (k5_xboole_0 @ X34 @ (k4_xboole_0 @ X35 @ X34)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.06/1.26  thf('22', plain,
% 1.06/1.26      (((k2_xboole_0 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1) @ sk_C_1)
% 1.06/1.26         = (k5_xboole_0 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1) @ sk_C_1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['20', '21'])).
% 1.06/1.26  thf(t91_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.06/1.26       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.06/1.26  thf('23', plain,
% 1.06/1.26      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 1.06/1.26           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.06/1.26  thf('24', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.26  thf(t92_xboole_1, axiom,
% 1.06/1.26    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.06/1.26  thf('25', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 1.06/1.26      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.06/1.26  thf('26', plain,
% 1.06/1.26      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 1.06/1.26           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.06/1.26  thf('27', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.26           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['25', '26'])).
% 1.06/1.26  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.26  thf('29', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.26  thf('30', plain,
% 1.06/1.26      (((k2_xboole_0 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1) @ sk_C_1) = (sk_B_1))),
% 1.06/1.26      inference('demod', [status(thm)], ['22', '23', '24', '29'])).
% 1.06/1.26  thf('31', plain, (((k2_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_B_1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['6', '30'])).
% 1.06/1.26  thf('32', plain,
% 1.06/1.26      (![X34 : $i, X35 : $i]:
% 1.06/1.26         ((k2_xboole_0 @ X34 @ X35)
% 1.06/1.26           = (k5_xboole_0 @ X34 @ (k4_xboole_0 @ X35 @ X34)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.06/1.26  thf('33', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.26  thf('34', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.26           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['32', '33'])).
% 1.06/1.26  thf('35', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (k5_xboole_0 @ sk_C_1 @ sk_B_1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['31', '34'])).
% 1.06/1.26  thf('36', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.26  thf('37', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.26  thf('38', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['36', '37'])).
% 1.06/1.26  thf('39', plain,
% 1.06/1.26      (((sk_C_1) = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['35', '38'])).
% 1.06/1.26  thf('40', plain,
% 1.06/1.26      (![X9 : $i, X10 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X9 @ X10)
% 1.06/1.26           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.26  thf('41', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.26  thf('42', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k3_xboole_0 @ X1 @ X0)
% 1.06/1.26           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['40', '41'])).
% 1.06/1.26  thf('43', plain, (((sk_C_1) = (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.06/1.26      inference('demod', [status(thm)], ['39', '42'])).
% 1.06/1.26  thf(t18_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.06/1.26  thf('44', plain,
% 1.06/1.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.06/1.26         ((r1_tarski @ X14 @ X15)
% 1.06/1.26          | ~ (r1_tarski @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.06/1.26  thf('45', plain,
% 1.06/1.26      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_1) | (r1_tarski @ X0 @ sk_B_1))),
% 1.06/1.26      inference('sup-', [status(thm)], ['43', '44'])).
% 1.06/1.26  thf('46', plain,
% 1.06/1.26      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ sk_B_1)),
% 1.06/1.26      inference('sup-', [status(thm)], ['1', '45'])).
% 1.06/1.26  thf('47', plain,
% 1.06/1.26      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 1.06/1.26      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.26  thf('48', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('49', plain,
% 1.06/1.26      (![X17 : $i, X18 : $i]:
% 1.06/1.26         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 1.06/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.06/1.26  thf('50', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['48', '49'])).
% 1.06/1.26  thf('51', plain,
% 1.06/1.26      (![X29 : $i, X30 : $i]:
% 1.06/1.26         ((k2_xboole_0 @ X29 @ X30)
% 1.06/1.26           = (k2_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 1.06/1.26              (k3_xboole_0 @ X29 @ X30)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t93_xboole_1])).
% 1.06/1.26  thf('52', plain,
% 1.06/1.26      (((k2_xboole_0 @ sk_A @ sk_B_1)
% 1.06/1.26         = (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B_1) @ sk_A))),
% 1.06/1.26      inference('sup+', [status(thm)], ['50', '51'])).
% 1.06/1.26  thf('53', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['48', '49'])).
% 1.06/1.26  thf('54', plain,
% 1.06/1.26      (![X7 : $i, X8 : $i]:
% 1.06/1.26         (r1_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k5_xboole_0 @ X7 @ X8))),
% 1.06/1.26      inference('cnf', [status(esa)], [l97_xboole_1])).
% 1.06/1.26  thf('55', plain, ((r1_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B_1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['53', '54'])).
% 1.06/1.26  thf('56', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['10', '11'])).
% 1.06/1.26  thf('57', plain,
% 1.06/1.26      (((k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['55', '56'])).
% 1.06/1.26  thf('58', plain,
% 1.06/1.26      (![X9 : $i, X10 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X9 @ X10)
% 1.06/1.26           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.26  thf('59', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B_1))
% 1.06/1.26         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['57', '58'])).
% 1.06/1.26  thf('60', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.26  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.26  thf('62', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.06/1.26  thf('63', plain,
% 1.06/1.26      (![X34 : $i, X35 : $i]:
% 1.06/1.26         ((k2_xboole_0 @ X34 @ X35)
% 1.06/1.26           = (k5_xboole_0 @ X34 @ (k4_xboole_0 @ X35 @ X34)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.06/1.26  thf('64', plain,
% 1.06/1.26      (((k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B_1) @ sk_A)
% 1.06/1.26         = (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B_1) @ sk_A))),
% 1.06/1.26      inference('sup+', [status(thm)], ['62', '63'])).
% 1.06/1.26  thf('65', plain,
% 1.06/1.26      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.06/1.26         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 1.06/1.26           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.06/1.26  thf('66', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.26  thf('67', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['27', '28'])).
% 1.06/1.26  thf('68', plain,
% 1.06/1.26      (((k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B_1) @ sk_A) = (sk_B_1))),
% 1.06/1.26      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 1.06/1.26  thf('69', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['52', '68'])).
% 1.06/1.26  thf('70', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.26           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['32', '33'])).
% 1.06/1.26  thf('71', plain,
% 1.06/1.26      (((k4_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['69', '70'])).
% 1.06/1.26  thf('72', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['36', '37'])).
% 1.06/1.26  thf('73', plain,
% 1.06/1.26      (((sk_A) = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_A)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['71', '72'])).
% 1.06/1.26  thf('74', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((k3_xboole_0 @ X1 @ X0)
% 1.06/1.26           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.26      inference('sup+', [status(thm)], ['40', '41'])).
% 1.06/1.26  thf('75', plain, (((sk_A) = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['73', '74'])).
% 1.06/1.26  thf('76', plain,
% 1.06/1.26      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.06/1.26         ((r1_tarski @ X14 @ X15)
% 1.06/1.26          | ~ (r1_tarski @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.06/1.26  thf('77', plain,
% 1.06/1.26      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_A) | (r1_tarski @ X0 @ sk_B_1))),
% 1.06/1.26      inference('sup-', [status(thm)], ['75', '76'])).
% 1.06/1.26  thf('78', plain,
% 1.06/1.26      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)),
% 1.06/1.26      inference('sup-', [status(thm)], ['47', '77'])).
% 1.06/1.26  thf(t97_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) & 
% 1.06/1.26         ( r1_tarski @ ( k4_xboole_0 @ B @ A ) @ C ) ) =>
% 1.06/1.26       ( r1_tarski @ ( k5_xboole_0 @ A @ B ) @ C ) ))).
% 1.06/1.26  thf('79', plain,
% 1.06/1.26      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.06/1.26         ((r1_tarski @ (k5_xboole_0 @ X31 @ X32) @ X33)
% 1.06/1.26          | ~ (r1_tarski @ (k4_xboole_0 @ X32 @ X31) @ X33)
% 1.06/1.26          | ~ (r1_tarski @ (k4_xboole_0 @ X31 @ X32) @ X33))),
% 1.06/1.26      inference('cnf', [status(esa)], [t97_xboole_1])).
% 1.06/1.26  thf('80', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B_1)
% 1.06/1.26          | (r1_tarski @ (k5_xboole_0 @ X0 @ sk_A) @ sk_B_1))),
% 1.06/1.26      inference('sup-', [status(thm)], ['78', '79'])).
% 1.06/1.26  thf('81', plain, ((r1_tarski @ (k5_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1)),
% 1.06/1.26      inference('sup-', [status(thm)], ['46', '80'])).
% 1.06/1.26  thf('82', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.06/1.26      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.26  thf('83', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1)),
% 1.06/1.26      inference('demod', [status(thm)], ['81', '82'])).
% 1.06/1.26  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 1.06/1.26  
% 1.06/1.26  % SZS output end Refutation
% 1.06/1.26  
% 1.06/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
