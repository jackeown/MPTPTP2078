%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cQTHsZhJOV

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:18 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 167 expanded)
%              Number of leaves         :   29 (  64 expanded)
%              Depth                    :   22
%              Number of atoms          :  598 (1062 expanded)
%              Number of equality atoms :   64 ( 109 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X59: $i,X60: $i] :
      ( r1_tarski @ ( k1_tarski @ X59 ) @ ( k2_tarski @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('30',plain,(
    ! [X23: $i] :
      ( r1_xboole_0 @ X23 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X23: $i] :
      ( r1_xboole_0 @ X23 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('34',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('36',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','38'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( v1_xboole_0 @ X25 )
      | ( X24 = X25 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','42'])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['16','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['6','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('64',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ( k2_tarski @ sk_A @ sk_B_1 )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cQTHsZhJOV
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:25:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 1.07/1.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.31  % Solved by: fo/fo7.sh
% 1.07/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.31  % done 1870 iterations in 0.867s
% 1.07/1.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.31  % SZS output start Refutation
% 1.07/1.31  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.07/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.31  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.07/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.31  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.07/1.31  thf(sk_B_type, type, sk_B: $i > $i).
% 1.07/1.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.07/1.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.07/1.31  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.07/1.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.07/1.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.07/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.31  thf(t14_zfmisc_1, conjecture,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 1.07/1.31       ( k2_tarski @ A @ B ) ))).
% 1.07/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.31    (~( ![A:$i,B:$i]:
% 1.07/1.31        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 1.07/1.31          ( k2_tarski @ A @ B ) ) )),
% 1.07/1.31    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 1.07/1.31  thf('0', plain,
% 1.07/1.31      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B_1))
% 1.07/1.31         != (k2_tarski @ sk_A @ sk_B_1))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(t12_zfmisc_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 1.07/1.31  thf('1', plain,
% 1.07/1.31      (![X59 : $i, X60 : $i]:
% 1.07/1.31         (r1_tarski @ (k1_tarski @ X59) @ (k2_tarski @ X59 @ X60))),
% 1.07/1.31      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.07/1.31  thf(t28_xboole_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.07/1.31  thf('2', plain,
% 1.07/1.31      (![X18 : $i, X19 : $i]:
% 1.07/1.31         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.07/1.31      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.07/1.31  thf('3', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 1.07/1.31           = (k1_tarski @ X1))),
% 1.07/1.31      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.31  thf(commutativity_k3_xboole_0, axiom,
% 1.07/1.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.07/1.31  thf('4', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.31  thf(t100_xboole_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.07/1.31  thf('5', plain,
% 1.07/1.31      (![X16 : $i, X17 : $i]:
% 1.07/1.31         ((k4_xboole_0 @ X16 @ X17)
% 1.07/1.31           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.31  thf('6', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((k4_xboole_0 @ X0 @ X1)
% 1.07/1.31           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.31      inference('sup+', [status(thm)], ['4', '5'])).
% 1.07/1.31  thf(d10_xboole_0, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.07/1.31  thf('7', plain,
% 1.07/1.31      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 1.07/1.31      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.07/1.31  thf('8', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 1.07/1.31      inference('simplify', [status(thm)], ['7'])).
% 1.07/1.31  thf('9', plain,
% 1.07/1.31      (![X18 : $i, X19 : $i]:
% 1.07/1.31         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.07/1.31      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.07/1.31  thf('10', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['8', '9'])).
% 1.07/1.31  thf('11', plain,
% 1.07/1.31      (![X16 : $i, X17 : $i]:
% 1.07/1.31         ((k4_xboole_0 @ X16 @ X17)
% 1.07/1.31           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.31  thf('12', plain,
% 1.07/1.31      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['10', '11'])).
% 1.07/1.31  thf(t91_xboole_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.07/1.31       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.07/1.31  thf('13', plain,
% 1.07/1.31      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.07/1.31         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 1.07/1.31           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.07/1.31  thf(commutativity_k5_xboole_0, axiom,
% 1.07/1.31    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.07/1.31  thf('14', plain,
% 1.07/1.31      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.07/1.31      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.07/1.31  thf('15', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.07/1.31           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.07/1.31      inference('sup+', [status(thm)], ['13', '14'])).
% 1.07/1.31  thf('16', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.07/1.31           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.07/1.31      inference('sup+', [status(thm)], ['12', '15'])).
% 1.07/1.31  thf('17', plain,
% 1.07/1.31      (![X16 : $i, X17 : $i]:
% 1.07/1.31         ((k4_xboole_0 @ X16 @ X17)
% 1.07/1.31           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.31  thf('18', plain,
% 1.07/1.31      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.07/1.31      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.07/1.31  thf(t5_boole, axiom,
% 1.07/1.31    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.07/1.31  thf('19', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.07/1.31      inference('cnf', [status(esa)], [t5_boole])).
% 1.07/1.31  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['18', '19'])).
% 1.07/1.31  thf('21', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['17', '20'])).
% 1.07/1.31  thf('22', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.31  thf('23', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['21', '22'])).
% 1.07/1.31  thf(d1_xboole_0, axiom,
% 1.07/1.31    (![A:$i]:
% 1.07/1.31     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.07/1.31  thf('24', plain,
% 1.07/1.31      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.07/1.31      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.07/1.31  thf('25', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['17', '20'])).
% 1.07/1.31  thf('26', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.31  thf(t4_xboole_0, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.07/1.31            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.07/1.31       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.07/1.31            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.07/1.31  thf('27', plain,
% 1.07/1.31      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.07/1.31         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 1.07/1.31          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.07/1.31      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.07/1.31  thf('28', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.07/1.31          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.07/1.31      inference('sup-', [status(thm)], ['26', '27'])).
% 1.07/1.31  thf('29', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 1.07/1.31          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['25', '28'])).
% 1.07/1.31  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.07/1.31  thf('30', plain, (![X23 : $i]: (r1_xboole_0 @ X23 @ k1_xboole_0)),
% 1.07/1.31      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.07/1.31  thf('31', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.31      inference('demod', [status(thm)], ['29', '30'])).
% 1.07/1.31  thf('32', plain,
% 1.07/1.31      (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['24', '31'])).
% 1.07/1.31  thf('33', plain, (![X23 : $i]: (r1_xboole_0 @ X23 @ k1_xboole_0)),
% 1.07/1.31      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.07/1.31  thf('34', plain,
% 1.07/1.31      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.07/1.31      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.07/1.31  thf('35', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['8', '9'])).
% 1.07/1.31  thf('36', plain,
% 1.07/1.31      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.07/1.31         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 1.07/1.31          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.07/1.31      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.07/1.31  thf('37', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['35', '36'])).
% 1.07/1.31  thf('38', plain,
% 1.07/1.31      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['34', '37'])).
% 1.07/1.31  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.31      inference('sup-', [status(thm)], ['33', '38'])).
% 1.07/1.31  thf(t8_boole, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.07/1.31  thf('40', plain,
% 1.07/1.31      (![X24 : $i, X25 : $i]:
% 1.07/1.31         (~ (v1_xboole_0 @ X24) | ~ (v1_xboole_0 @ X25) | ((X24) = (X25)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t8_boole])).
% 1.07/1.31  thf('41', plain,
% 1.07/1.31      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('42', plain,
% 1.07/1.31      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['32', '41'])).
% 1.07/1.31  thf('43', plain,
% 1.07/1.31      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.31      inference('demod', [status(thm)], ['23', '42'])).
% 1.07/1.31  thf('44', plain,
% 1.07/1.31      (![X16 : $i, X17 : $i]:
% 1.07/1.31         ((k4_xboole_0 @ X16 @ X17)
% 1.07/1.31           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.31  thf('45', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['43', '44'])).
% 1.07/1.31  thf(t98_xboole_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.07/1.31  thf('46', plain,
% 1.07/1.31      (![X29 : $i, X30 : $i]:
% 1.07/1.31         ((k2_xboole_0 @ X29 @ X30)
% 1.07/1.31           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.07/1.31  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['18', '19'])).
% 1.07/1.31  thf('48', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['46', '47'])).
% 1.07/1.31  thf('49', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.31      inference('demod', [status(thm)], ['45', '48'])).
% 1.07/1.31  thf('50', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.07/1.31      inference('cnf', [status(esa)], [t5_boole])).
% 1.07/1.31  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['49', '50'])).
% 1.07/1.31  thf(t40_xboole_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.07/1.31  thf('52', plain,
% 1.07/1.31      (![X20 : $i, X21 : $i]:
% 1.07/1.31         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 1.07/1.31           = (k4_xboole_0 @ X20 @ X21))),
% 1.07/1.31      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.07/1.31  thf('53', plain,
% 1.07/1.31      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['51', '52'])).
% 1.07/1.31  thf('54', plain,
% 1.07/1.31      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['32', '41'])).
% 1.07/1.31  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.07/1.31      inference('demod', [status(thm)], ['53', '54'])).
% 1.07/1.31  thf('56', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.07/1.31      inference('cnf', [status(esa)], [t5_boole])).
% 1.07/1.31  thf('57', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 1.07/1.31      inference('sup+', [status(thm)], ['55', '56'])).
% 1.07/1.31  thf('58', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.07/1.31      inference('demod', [status(thm)], ['16', '57'])).
% 1.07/1.31  thf('59', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 1.07/1.31           = (X1))),
% 1.07/1.31      inference('sup+', [status(thm)], ['6', '58'])).
% 1.07/1.31  thf('60', plain,
% 1.07/1.31      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.07/1.31      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.07/1.31  thf('61', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 1.07/1.31           = (X1))),
% 1.07/1.31      inference('demod', [status(thm)], ['59', '60'])).
% 1.07/1.31  thf('62', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((k5_xboole_0 @ 
% 1.07/1.31           (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)) @ 
% 1.07/1.31           (k1_tarski @ X0)) = (k2_tarski @ X0 @ X1))),
% 1.07/1.31      inference('sup+', [status(thm)], ['3', '61'])).
% 1.07/1.31  thf('63', plain,
% 1.07/1.31      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.07/1.31      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.07/1.31  thf('64', plain,
% 1.07/1.31      (![X29 : $i, X30 : $i]:
% 1.07/1.31         ((k2_xboole_0 @ X29 @ X30)
% 1.07/1.31           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.07/1.31  thf('65', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 1.07/1.31           = (k2_tarski @ X0 @ X1))),
% 1.07/1.31      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.07/1.31  thf('66', plain,
% 1.07/1.31      (((k2_tarski @ sk_A @ sk_B_1) != (k2_tarski @ sk_A @ sk_B_1))),
% 1.07/1.31      inference('demod', [status(thm)], ['0', '65'])).
% 1.07/1.31  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 1.07/1.31  
% 1.07/1.31  % SZS output end Refutation
% 1.07/1.31  
% 1.07/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
