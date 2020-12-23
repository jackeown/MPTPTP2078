%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k6Rmq8zXI3

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:46 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 880 expanded)
%              Number of leaves         :   28 ( 298 expanded)
%              Depth                    :   20
%              Number of atoms          :  731 (6120 expanded)
%              Number of equality atoms :   59 ( 559 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(t19_ordinal1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_ordinal1 @ C )
     => ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ B @ C ) )
       => ( r2_hidden @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_ordinal1 @ C )
       => ( ( ( r2_hidden @ A @ B )
            & ( r2_hidden @ B @ C ) )
         => ( r2_hidden @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X36 @ X38 ) @ X39 )
        = ( k1_tarski @ X36 ) )
      | ( X36 != X38 )
      | ( r2_hidden @ X36 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('3',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ X39 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X38 @ X38 ) @ X39 )
        = ( k1_tarski @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( r2_hidden @ X69 @ X70 )
      | ( r1_tarski @ X69 @ X70 )
      | ~ ( v1_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('6',plain,
    ( ~ ( v1_ordinal1 @ sk_C )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X21 @ ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X21 @ ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ ( k5_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','56'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','71'])).

thf('73',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X21 @ ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','71'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','71'])).

thf('79',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ X39 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X38 @ X38 ) @ X39 )
        = ( k1_tarski @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('82',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X46 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('83',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X46 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','86'])).

thf('88',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['1','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k6Rmq8zXI3
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:55:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 571 iterations in 0.198s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.46/0.66  thf(t19_ordinal1, conjecture,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( v1_ordinal1 @ C ) =>
% 0.46/0.66       ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.46/0.66         ( r2_hidden @ A @ C ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.66        ( ( v1_ordinal1 @ C ) =>
% 0.46/0.66          ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.46/0.66            ( r2_hidden @ A @ C ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t19_ordinal1])).
% 0.46/0.66  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(l38_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.66       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.46/0.66         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ (k2_tarski @ X36 @ X38) @ X39) = (k1_tarski @ X36))
% 0.46/0.66          | ((X36) != (X38))
% 0.46/0.66          | (r2_hidden @ X36 @ X39))),
% 0.46/0.66      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i]:
% 0.46/0.66         ((r2_hidden @ X38 @ X39)
% 0.46/0.66          | ((k4_xboole_0 @ (k2_tarski @ X38 @ X38) @ X39) = (k1_tarski @ X38)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.66  thf('4', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d2_ordinal1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_ordinal1 @ A ) <=>
% 0.46/0.66       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X69 : $i, X70 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X69 @ X70)
% 0.46/0.66          | (r1_tarski @ X69 @ X70)
% 0.46/0.66          | ~ (v1_ordinal1 @ X70))),
% 0.46/0.66      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.46/0.66  thf('6', plain, ((~ (v1_ordinal1 @ sk_C) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('7', plain, ((v1_ordinal1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('8', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(l32_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X2 : $i, X4 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.66  thf('10', plain, (((k4_xboole_0 @ sk_B_1 @ sk_C) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf(t81_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.46/0.66       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.46/0.66          | ~ (r1_xboole_0 @ X21 @ (k4_xboole_0 @ X20 @ X22)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.46/0.66          | (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf(t22_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)) = (X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.46/0.66  thf(t21_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X9 : $i, X10 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.46/0.66  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.66  thf('16', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.66  thf(t107_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.46/0.66       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.66         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7))
% 0.46/0.66          | ~ (r1_tarski @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.66  thf('19', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.66      inference('sup+', [status(thm)], ['15', '18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.46/0.66          | ~ (r1_xboole_0 @ X21 @ (k4_xboole_0 @ X20 @ X22)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.66  thf('22', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X2 : $i, X4 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('25', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '24'])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X0 : $i]: (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['12', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['3', '26'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf(d6_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k5_xboole_0 @ A @ B ) =
% 0.46/0.66       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.46/0.66           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.66  thf(t45_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) =>
% 0.46/0.66       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         (((X17) = (k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))
% 0.46/0.66          | ~ (r1_tarski @ X16 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf(t40_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.66           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i]:
% 0.46/0.66         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.46/0.66          | (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.66          | (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['34', '37'])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 0.46/0.66      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['33', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['41', '44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.66         ((r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 0.46/0.66          | ~ (r1_tarski @ X5 @ (k5_xboole_0 @ X6 @ X7)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X1 @ X0)
% 0.46/0.66          | (r1_tarski @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (r1_tarski @ X0 @ 
% 0.46/0.66          (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('50', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.66      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X2 : $i, X4 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.66  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.66  thf(t51_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.46/0.66       ( A ) ))).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.46/0.66           = (X18))),
% 0.46/0.66      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.66  thf('55', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['30', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['30', '56'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.66  thf('61', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.66      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X1 @ X0)
% 0.46/0.66          | (r1_tarski @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X0 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         (((X17) = (k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))
% 0.46/0.66          | ~ (r1_tarski @ X16 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k2_xboole_0 @ X0 @ 
% 0.46/0.66              (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.46/0.66           = (k4_xboole_0 @ X14 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.46/0.66  thf('69', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.66  thf('70', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.66  thf('71', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['60', '70'])).
% 0.46/0.66  thf('72', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['57', '71'])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.46/0.66          | ~ (r1_xboole_0 @ X21 @ (k4_xboole_0 @ X20 @ X22)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_xboole_0 @ X1 @ X0)
% 0.46/0.66          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.66  thf('75', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['57', '71'])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.66  thf('77', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ X0 @ sk_C) | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['27', '76'])).
% 0.46/0.66  thf('78', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['57', '71'])).
% 0.46/0.66  thf('79', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i]:
% 0.46/0.66         ((r2_hidden @ X38 @ X39)
% 0.46/0.66          | ((k4_xboole_0 @ (k2_tarski @ X38 @ X38) @ X39) = (k1_tarski @ X38)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))
% 0.46/0.66          | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['78', '79'])).
% 0.46/0.66  thf('81', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '24'])).
% 0.46/0.66  thf(t55_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.46/0.66         (~ (r1_xboole_0 @ (k2_tarski @ X46 @ X47) @ X48)
% 0.46/0.66          | ~ (r2_hidden @ X46 @ X48))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.46/0.66  thf('83', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.66  thf('84', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.46/0.66      inference('clc', [status(thm)], ['80', '83'])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.46/0.66         (~ (r1_xboole_0 @ (k2_tarski @ X46 @ X47) @ X48)
% 0.46/0.66          | ~ (r2_hidden @ X46 @ X48))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.46/0.66  thf('86', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['84', '85'])).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['77', '86'])).
% 0.46/0.66  thf('88', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '87'])).
% 0.46/0.66  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
