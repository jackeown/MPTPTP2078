%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YeZHZhNopT

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:37 EST 2020

% Result     : Theorem 3.13s
% Output     : Refutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  305 (9784 expanded)
%              Number of leaves         :   33 (3213 expanded)
%              Depth                    :   38
%              Number of atoms          : 2385 (81472 expanded)
%              Number of equality atoms :  352 (10933 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('6',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k3_tarski @ ( k2_tarski @ X20 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X61: $i,X62: $i] :
      ( ( X62
        = ( k1_tarski @ X61 ) )
      | ( X62 = k1_xboole_0 )
      | ~ ( r1_tarski @ X62 @ ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('13',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) )
      = X16 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B )
    | ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) )
      = X16 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('23',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      = X18 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k3_tarski @ ( k2_tarski @ X20 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = sk_B )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['11','14'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = sk_B )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('36',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B )
        = sk_A )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B )
        = sk_A )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ( ( k3_tarski @ sk_B )
        = sk_A ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k3_tarski @ sk_B )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      = X18 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('48',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      = X18 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) )
      = X16 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('64',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('69',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['62','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('79',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','79'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('81',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ X31 @ X32 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X31 @ X32 ) @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('82',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('83',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('84',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['80','84'])).

thf('86',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('90',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('94',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','97','98','101'])).

thf('103',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['89','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('107',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['87','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) )
        = X0 )
      | ( ( k3_tarski @ sk_B )
        = sk_A ) ) ),
    inference('sup+',[status(thm)],['45','113'])).

thf('115',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( ( k3_tarski @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['3','114'])).

thf('116',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['116'])).

thf('119',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['119'])).

thf('121',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('122',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('123',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X61: $i,X62: $i] :
      ( ( X62
        = ( k1_tarski @ X61 ) )
      | ( X62 = k1_xboole_0 )
      | ~ ( r1_tarski @ X62 @ ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('125',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['126'])).

thf('128',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','127'])).

thf('129',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['116'])).

thf('131',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['118','120','132'])).

thf('134',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['117','133'])).

thf('135',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['115','134'])).

thf('136',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('138',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['115','134'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k1_tarski @ ( k3_tarski @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('145',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('146',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      = X18 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) ) )
        = sk_B )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['143','150'])).

thf('152',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['11','14'])).

thf('153',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['115','134'])).

thf('154',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('161',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','111'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['159','164'])).

thf('166',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['151','154','169','172'])).

thf('174',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ sk_B ) ) )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) )
        = X0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
      = sk_C_2 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['136','177'])).

thf('179',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['117','133'])).

thf('180',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['115','134'])).

thf('181',plain,(
    sk_C_2
 != ( k1_tarski @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['178','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('184',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('187',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('189',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','135'])).

thf('191',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('192',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('194',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('196',plain,
    ( ( ( k3_tarski @ sk_B )
      = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('198',plain,
    ( ( sk_B
      = ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ ( k3_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('202',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( k5_xboole_0 @ sk_C_2 @ sk_B )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['199','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('205',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('207',plain,
    ( ( sk_C_2
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('210',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['126'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('213',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('214',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('215',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('216',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('218',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ X0 @ X1 )
        = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ X1 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_B @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['213','218'])).

thf('220',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('222',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('224',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('226',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_B @ X0 ) )
        = X1 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['219','224','225'])).

thf('227',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['212','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('229',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('231',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k3_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('233',plain,
    ( ! [X0: $i] :
        ( ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ sk_B ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('235',plain,
    ( ! [X0: $i] :
        ( ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) )
        = ( k5_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('237',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('239',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k5_xboole_0 @ X31 @ ( k5_xboole_0 @ X32 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('240',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ X0 @ X1 )
        = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ X1 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('241',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ sk_B ) )
        = ( k3_tarski @ ( k2_tarski @ X0 @ sk_B ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('243',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_B )
        = ( k3_tarski @ ( k2_tarski @ X0 @ sk_B ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) )
      = X16 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('245',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ sk_B ) )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('247',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ X1 )
        = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['245','246'])).

thf('248',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ sk_B )
        = ( k3_tarski @ ( k2_tarski @ X0 @ sk_B ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('249',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('250',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('251',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ sk_B ) )
        = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['248','251'])).

thf('253',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('254',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ sk_B ) )
        = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k5_xboole_0 @ sk_B @ X1 )
        = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['247','254'])).

thf('256',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ X0 ) )
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['238','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('259',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['256','257','258'])).

thf('260',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['237','259'])).

thf('261',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['117','133'])).

thf('262',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['260','261'])).

thf('263',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['126'])).

thf('264',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['262','263'])).

thf('265',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['211','264'])).

thf('266',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['210','265'])).

thf('267',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['193','266'])).

thf('268',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['192','267'])).

thf('269',plain,(
    sk_C_2
 != ( k1_tarski @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('270',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['268','269'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YeZHZhNopT
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:32:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.13/3.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.13/3.37  % Solved by: fo/fo7.sh
% 3.13/3.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.13/3.37  % done 4095 iterations in 2.925s
% 3.13/3.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.13/3.37  % SZS output start Refutation
% 3.13/3.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.13/3.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.13/3.37  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.13/3.37  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.13/3.37  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.13/3.37  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.13/3.37  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.13/3.37  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.13/3.37  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.13/3.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.13/3.37  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.13/3.37  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.13/3.37  thf(sk_B_type, type, sk_B: $i).
% 3.13/3.37  thf(sk_A_type, type, sk_A: $i).
% 3.13/3.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.13/3.37  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.13/3.37  thf(t43_zfmisc_1, conjecture,
% 3.13/3.37    (![A:$i,B:$i,C:$i]:
% 3.13/3.37     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 3.13/3.37          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.13/3.37          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.13/3.37          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 3.13/3.37  thf(zf_stmt_0, negated_conjecture,
% 3.13/3.37    (~( ![A:$i,B:$i,C:$i]:
% 3.13/3.37        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 3.13/3.37             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.13/3.37             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.13/3.37             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 3.13/3.37    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 3.13/3.37  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 3.13/3.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.37  thf(l51_zfmisc_1, axiom,
% 3.13/3.37    (![A:$i,B:$i]:
% 3.13/3.37     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.13/3.37  thf('1', plain,
% 3.13/3.37      (![X64 : $i, X65 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 3.13/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.13/3.37  thf('2', plain,
% 3.13/3.37      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 3.13/3.37      inference('demod', [status(thm)], ['0', '1'])).
% 3.13/3.37  thf('3', plain,
% 3.13/3.37      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 3.13/3.37      inference('demod', [status(thm)], ['0', '1'])).
% 3.13/3.37  thf('4', plain,
% 3.13/3.37      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 3.13/3.37      inference('demod', [status(thm)], ['0', '1'])).
% 3.13/3.37  thf(t29_xboole_1, axiom,
% 3.13/3.37    (![A:$i,B:$i,C:$i]:
% 3.13/3.37     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 3.13/3.37  thf('5', plain,
% 3.13/3.37      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.13/3.37         (r1_tarski @ (k3_xboole_0 @ X20 @ X21) @ (k2_xboole_0 @ X20 @ X22))),
% 3.13/3.37      inference('cnf', [status(esa)], [t29_xboole_1])).
% 3.13/3.37  thf('6', plain,
% 3.13/3.37      (![X64 : $i, X65 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 3.13/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.13/3.37  thf('7', plain,
% 3.13/3.37      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.13/3.37         (r1_tarski @ (k3_xboole_0 @ X20 @ X21) @ 
% 3.13/3.37          (k3_tarski @ (k2_tarski @ X20 @ X22)))),
% 3.13/3.37      inference('demod', [status(thm)], ['5', '6'])).
% 3.13/3.37  thf('8', plain,
% 3.13/3.37      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (k1_tarski @ sk_A))),
% 3.13/3.37      inference('sup+', [status(thm)], ['4', '7'])).
% 3.13/3.37  thf(l3_zfmisc_1, axiom,
% 3.13/3.37    (![A:$i,B:$i]:
% 3.13/3.37     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 3.13/3.37       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 3.13/3.37  thf('9', plain,
% 3.13/3.37      (![X61 : $i, X62 : $i]:
% 3.13/3.37         (((X62) = (k1_tarski @ X61))
% 3.13/3.37          | ((X62) = (k1_xboole_0))
% 3.13/3.37          | ~ (r1_tarski @ X62 @ (k1_tarski @ X61)))),
% 3.13/3.37      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 3.13/3.37  thf('10', plain,
% 3.13/3.37      (![X0 : $i]:
% 3.13/3.37         (((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 3.13/3.37          | ((k3_xboole_0 @ sk_B @ X0) = (k1_tarski @ sk_A)))),
% 3.13/3.37      inference('sup-', [status(thm)], ['8', '9'])).
% 3.13/3.37  thf('11', plain,
% 3.13/3.37      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 3.13/3.37      inference('demod', [status(thm)], ['0', '1'])).
% 3.13/3.37  thf(t21_xboole_1, axiom,
% 3.13/3.37    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 3.13/3.37  thf('12', plain,
% 3.13/3.37      (![X16 : $i, X17 : $i]:
% 3.13/3.37         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (X16))),
% 3.13/3.37      inference('cnf', [status(esa)], [t21_xboole_1])).
% 3.13/3.37  thf('13', plain,
% 3.13/3.37      (![X64 : $i, X65 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 3.13/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.13/3.37  thf('14', plain,
% 3.13/3.37      (![X16 : $i, X17 : $i]:
% 3.13/3.37         ((k3_xboole_0 @ X16 @ (k3_tarski @ (k2_tarski @ X16 @ X17))) = (X16))),
% 3.13/3.37      inference('demod', [status(thm)], ['12', '13'])).
% 3.13/3.37  thf('15', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 3.13/3.37      inference('sup+', [status(thm)], ['11', '14'])).
% 3.13/3.37  thf('16', plain,
% 3.13/3.37      ((((k1_tarski @ sk_A) = (sk_B))
% 3.13/3.37        | ((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 3.13/3.37      inference('sup+', [status(thm)], ['10', '15'])).
% 3.13/3.37  thf(d7_xboole_0, axiom,
% 3.13/3.37    (![A:$i,B:$i]:
% 3.13/3.37     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.13/3.37       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.13/3.37  thf('17', plain,
% 3.13/3.37      (![X4 : $i, X6 : $i]:
% 3.13/3.37         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 3.13/3.37      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.13/3.37  thf('18', plain,
% 3.13/3.37      ((((k1_xboole_0) != (k1_xboole_0))
% 3.13/3.37        | ((k1_tarski @ sk_A) = (sk_B))
% 3.13/3.37        | (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 3.13/3.37      inference('sup-', [status(thm)], ['16', '17'])).
% 3.13/3.37  thf('19', plain,
% 3.13/3.37      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 3.13/3.37        | ((k1_tarski @ sk_A) = (sk_B)))),
% 3.13/3.37      inference('simplify', [status(thm)], ['18'])).
% 3.13/3.37  thf(t4_xboole_0, axiom,
% 3.13/3.37    (![A:$i,B:$i]:
% 3.13/3.37     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 3.13/3.37            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.13/3.37       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.13/3.37            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 3.13/3.37  thf('20', plain,
% 3.13/3.37      (![X7 : $i, X8 : $i]:
% 3.13/3.37         ((r1_xboole_0 @ X7 @ X8)
% 3.13/3.37          | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ (k3_xboole_0 @ X7 @ X8)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.13/3.37  thf('21', plain,
% 3.13/3.37      (![X16 : $i, X17 : $i]:
% 3.13/3.37         ((k3_xboole_0 @ X16 @ (k3_tarski @ (k2_tarski @ X16 @ X17))) = (X16))),
% 3.13/3.37      inference('demod', [status(thm)], ['12', '13'])).
% 3.13/3.37  thf(t22_xboole_1, axiom,
% 3.13/3.37    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 3.13/3.37  thf('22', plain,
% 3.13/3.37      (![X18 : $i, X19 : $i]:
% 3.13/3.37         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)) = (X18))),
% 3.13/3.37      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.13/3.37  thf('23', plain,
% 3.13/3.37      (![X64 : $i, X65 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 3.13/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.13/3.37  thf('24', plain,
% 3.13/3.37      (![X18 : $i, X19 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X18 @ (k3_xboole_0 @ X18 @ X19))) = (X18))),
% 3.13/3.37      inference('demod', [status(thm)], ['22', '23'])).
% 3.13/3.37  thf('25', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['21', '24'])).
% 3.13/3.37  thf('26', plain,
% 3.13/3.37      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.13/3.37         (r1_tarski @ (k3_xboole_0 @ X20 @ X21) @ 
% 3.13/3.37          (k3_tarski @ (k2_tarski @ X20 @ X22)))),
% 3.13/3.37      inference('demod', [status(thm)], ['5', '6'])).
% 3.13/3.37  thf('27', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 3.13/3.37      inference('sup+', [status(thm)], ['25', '26'])).
% 3.13/3.37  thf(d3_tarski, axiom,
% 3.13/3.37    (![A:$i,B:$i]:
% 3.13/3.37     ( ( r1_tarski @ A @ B ) <=>
% 3.13/3.37       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.13/3.37  thf('28', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.37         (~ (r2_hidden @ X0 @ X1)
% 3.13/3.37          | (r2_hidden @ X0 @ X2)
% 3.13/3.37          | ~ (r1_tarski @ X1 @ X2))),
% 3.13/3.37      inference('cnf', [status(esa)], [d3_tarski])).
% 3.13/3.37  thf('29', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.37         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.13/3.37      inference('sup-', [status(thm)], ['27', '28'])).
% 3.13/3.37  thf('30', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]:
% 3.13/3.37         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1))),
% 3.13/3.37      inference('sup-', [status(thm)], ['20', '29'])).
% 3.13/3.37  thf('31', plain,
% 3.13/3.37      (![X7 : $i, X9 : $i, X10 : $i]:
% 3.13/3.37         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 3.13/3.37          | ~ (r1_xboole_0 @ X7 @ X10))),
% 3.13/3.37      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.13/3.37  thf('32', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.37         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.13/3.37          | ~ (r1_xboole_0 @ X1 @ X0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['30', '31'])).
% 3.13/3.37  thf('33', plain,
% 3.13/3.37      (![X0 : $i]:
% 3.13/3.37         (((k1_tarski @ sk_A) = (sk_B))
% 3.13/3.37          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['19', '32'])).
% 3.13/3.37  thf('34', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 3.13/3.37      inference('sup+', [status(thm)], ['11', '14'])).
% 3.13/3.37  thf('35', plain,
% 3.13/3.37      (![X0 : $i]: (((k1_tarski @ sk_A) = (sk_B)) | (r1_xboole_0 @ sk_B @ X0))),
% 3.13/3.37      inference('demod', [status(thm)], ['33', '34'])).
% 3.13/3.37  thf(t69_enumset1, axiom,
% 3.13/3.37    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.13/3.37  thf('36', plain,
% 3.13/3.37      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 3.13/3.37      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.13/3.37  thf('37', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['21', '24'])).
% 3.13/3.37  thf('38', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['36', '37'])).
% 3.13/3.37  thf('39', plain,
% 3.13/3.37      (![X0 : $i]: (((k3_tarski @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_B @ X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['35', '38'])).
% 3.13/3.37  thf('40', plain,
% 3.13/3.37      (![X4 : $i, X5 : $i]:
% 3.13/3.37         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 3.13/3.37      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.13/3.37  thf('41', plain,
% 3.13/3.37      (![X0 : $i]:
% 3.13/3.37         (((k3_tarski @ sk_B) = (sk_A))
% 3.13/3.37          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 3.13/3.37      inference('sup-', [status(thm)], ['39', '40'])).
% 3.13/3.37  thf(t100_xboole_1, axiom,
% 3.13/3.37    (![A:$i,B:$i]:
% 3.13/3.37     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.13/3.37  thf('42', plain,
% 3.13/3.37      (![X14 : $i, X15 : $i]:
% 3.13/3.37         ((k4_xboole_0 @ X14 @ X15)
% 3.13/3.37           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.13/3.37  thf('43', plain,
% 3.13/3.37      (![X0 : $i]:
% 3.13/3.37         (((k4_xboole_0 @ sk_B @ X0) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 3.13/3.37          | ((k3_tarski @ sk_B) = (sk_A)))),
% 3.13/3.37      inference('sup+', [status(thm)], ['41', '42'])).
% 3.13/3.37  thf(t5_boole, axiom,
% 3.13/3.37    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.13/3.37  thf('44', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.37      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.37  thf('45', plain,
% 3.13/3.37      (![X0 : $i]:
% 3.13/3.37         (((k4_xboole_0 @ sk_B @ X0) = (sk_B)) | ((k3_tarski @ sk_B) = (sk_A)))),
% 3.13/3.37      inference('demod', [status(thm)], ['43', '44'])).
% 3.13/3.37  thf('46', plain,
% 3.13/3.37      (![X18 : $i, X19 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X18 @ (k3_xboole_0 @ X18 @ X19))) = (X18))),
% 3.13/3.37      inference('demod', [status(thm)], ['22', '23'])).
% 3.13/3.37  thf(t7_xboole_1, axiom,
% 3.13/3.37    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.13/3.37  thf('47', plain,
% 3.13/3.37      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 3.13/3.37      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.13/3.37  thf('48', plain,
% 3.13/3.37      (![X64 : $i, X65 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 3.13/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.13/3.37  thf('49', plain,
% 3.13/3.37      (![X26 : $i, X27 : $i]:
% 3.13/3.37         (r1_tarski @ X26 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))),
% 3.13/3.37      inference('demod', [status(thm)], ['47', '48'])).
% 3.13/3.37  thf('50', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.13/3.37      inference('sup+', [status(thm)], ['46', '49'])).
% 3.13/3.37  thf(l32_xboole_1, axiom,
% 3.13/3.37    (![A:$i,B:$i]:
% 3.13/3.37     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.13/3.37  thf('51', plain,
% 3.13/3.37      (![X11 : $i, X13 : $i]:
% 3.13/3.37         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 3.13/3.37          | ~ (r1_tarski @ X11 @ X13))),
% 3.13/3.37      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.13/3.37  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.37  thf('53', plain,
% 3.13/3.37      (![X18 : $i, X19 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X18 @ (k3_xboole_0 @ X18 @ X19))) = (X18))),
% 3.13/3.37      inference('demod', [status(thm)], ['22', '23'])).
% 3.13/3.37  thf('54', plain,
% 3.13/3.37      (![X16 : $i, X17 : $i]:
% 3.13/3.37         ((k3_xboole_0 @ X16 @ (k3_tarski @ (k2_tarski @ X16 @ X17))) = (X16))),
% 3.13/3.37      inference('demod', [status(thm)], ['12', '13'])).
% 3.13/3.37  thf('55', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['53', '54'])).
% 3.13/3.37  thf('56', plain,
% 3.13/3.37      (![X14 : $i, X15 : $i]:
% 3.13/3.37         ((k4_xboole_0 @ X14 @ X15)
% 3.13/3.37           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.13/3.37  thf('57', plain,
% 3.13/3.37      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['55', '56'])).
% 3.13/3.37  thf('58', plain,
% 3.13/3.37      (![X14 : $i, X15 : $i]:
% 3.13/3.37         ((k4_xboole_0 @ X14 @ X15)
% 3.13/3.37           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.13/3.37  thf('59', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.37      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.37  thf(t91_xboole_1, axiom,
% 3.13/3.37    (![A:$i,B:$i,C:$i]:
% 3.13/3.37     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 3.13/3.37       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 3.13/3.37  thf('60', plain,
% 3.13/3.37      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.37         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 3.13/3.37           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.13/3.37  thf('61', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]:
% 3.13/3.37         ((k5_xboole_0 @ X0 @ X1)
% 3.13/3.37           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 3.13/3.37      inference('sup+', [status(thm)], ['59', '60'])).
% 3.13/3.37  thf('62', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]:
% 3.13/3.37         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 3.13/3.37           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.13/3.37      inference('sup+', [status(thm)], ['58', '61'])).
% 3.13/3.37  thf('63', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['53', '54'])).
% 3.13/3.37  thf('64', plain,
% 3.13/3.37      (![X4 : $i, X6 : $i]:
% 3.13/3.37         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 3.13/3.37      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.13/3.37  thf('65', plain,
% 3.13/3.37      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['63', '64'])).
% 3.13/3.37  thf('66', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.13/3.37      inference('simplify', [status(thm)], ['65'])).
% 3.13/3.37  thf('67', plain,
% 3.13/3.37      (![X1 : $i, X3 : $i]:
% 3.13/3.37         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.13/3.37      inference('cnf', [status(esa)], [d3_tarski])).
% 3.13/3.37  thf('68', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['53', '54'])).
% 3.13/3.37  thf('69', plain,
% 3.13/3.37      (![X7 : $i, X9 : $i, X10 : $i]:
% 3.13/3.37         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 3.13/3.37          | ~ (r1_xboole_0 @ X7 @ X10))),
% 3.13/3.37      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.13/3.37  thf('70', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]:
% 3.13/3.37         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['68', '69'])).
% 3.13/3.37  thf('71', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r1_xboole_0 @ X0 @ X0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['67', '70'])).
% 3.13/3.37  thf('72', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.13/3.37      inference('sup-', [status(thm)], ['66', '71'])).
% 3.13/3.37  thf('73', plain,
% 3.13/3.37      (![X11 : $i, X13 : $i]:
% 3.13/3.37         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 3.13/3.37          | ~ (r1_tarski @ X11 @ X13))),
% 3.13/3.37      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.13/3.37  thf('74', plain,
% 3.13/3.37      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['72', '73'])).
% 3.13/3.37  thf('75', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.37      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.37  thf('76', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]:
% 3.13/3.37         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) = (X1))),
% 3.13/3.37      inference('demod', [status(thm)], ['62', '74', '75'])).
% 3.13/3.37  thf('77', plain,
% 3.13/3.37      (![X0 : $i]:
% 3.13/3.37         ((k4_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 3.13/3.37           (k3_xboole_0 @ k1_xboole_0 @ X0)) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['57', '76'])).
% 3.13/3.37  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.37  thf('79', plain,
% 3.13/3.37      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 3.13/3.37      inference('demod', [status(thm)], ['77', '78'])).
% 3.13/3.37  thf('80', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]:
% 3.13/3.37         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 3.13/3.37      inference('sup+', [status(thm)], ['52', '79'])).
% 3.13/3.37  thf(t94_xboole_1, axiom,
% 3.13/3.37    (![A:$i,B:$i]:
% 3.13/3.37     ( ( k2_xboole_0 @ A @ B ) =
% 3.13/3.37       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.13/3.37  thf('81', plain,
% 3.13/3.37      (![X31 : $i, X32 : $i]:
% 3.13/3.37         ((k2_xboole_0 @ X31 @ X32)
% 3.13/3.37           = (k5_xboole_0 @ (k5_xboole_0 @ X31 @ X32) @ 
% 3.13/3.37              (k3_xboole_0 @ X31 @ X32)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t94_xboole_1])).
% 3.13/3.37  thf('82', plain,
% 3.13/3.37      (![X64 : $i, X65 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 3.13/3.37      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.13/3.37  thf('83', plain,
% 3.13/3.37      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.37         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 3.13/3.37           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.13/3.37  thf('84', plain,
% 3.13/3.37      (![X31 : $i, X32 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 3.13/3.37           = (k5_xboole_0 @ X31 @ 
% 3.13/3.37              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 3.13/3.37      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.13/3.37  thf('85', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0))
% 3.13/3.37           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ 
% 3.13/3.37              (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.13/3.37      inference('sup+', [status(thm)], ['80', '84'])).
% 3.13/3.37  thf('86', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.37      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.37  thf('87', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0))
% 3.13/3.37           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 3.13/3.37      inference('demod', [status(thm)], ['85', '86'])).
% 3.13/3.37  thf('88', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.37  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.37  thf('90', plain,
% 3.13/3.37      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.37         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 3.13/3.37           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.13/3.37  thf('91', plain,
% 3.13/3.37      (![X14 : $i, X15 : $i]:
% 3.13/3.37         ((k4_xboole_0 @ X14 @ X15)
% 3.13/3.37           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.13/3.37  thf('92', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.37         ((k4_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)
% 3.13/3.37           = (k5_xboole_0 @ X2 @ 
% 3.13/3.37              (k5_xboole_0 @ X1 @ (k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))))),
% 3.13/3.37      inference('sup+', [status(thm)], ['90', '91'])).
% 3.13/3.37  thf('93', plain,
% 3.13/3.37      (![X31 : $i, X32 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 3.13/3.37           = (k5_xboole_0 @ X31 @ 
% 3.13/3.37              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 3.13/3.37      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.13/3.37  thf('94', plain,
% 3.13/3.37      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.37         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 3.13/3.37           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 3.13/3.37      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.13/3.37  thf('95', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ (k5_xboole_0 @ X2 @ X1) @ X0))
% 3.13/3.37           = (k5_xboole_0 @ X2 @ 
% 3.13/3.37              (k5_xboole_0 @ X1 @ 
% 3.13/3.37               (k5_xboole_0 @ X0 @ (k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)))))),
% 3.13/3.37      inference('sup+', [status(thm)], ['93', '94'])).
% 3.13/3.37  thf('96', plain,
% 3.13/3.37      (![X0 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0))
% 3.13/3.37           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)))),
% 3.13/3.37      inference('sup+', [status(thm)], ['92', '95'])).
% 3.13/3.37  thf('97', plain,
% 3.13/3.37      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['55', '56'])).
% 3.13/3.37  thf('98', plain,
% 3.13/3.37      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['55', '56'])).
% 3.13/3.37  thf('99', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.37  thf('100', plain,
% 3.13/3.37      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.13/3.37      inference('sup-', [status(thm)], ['72', '73'])).
% 3.13/3.37  thf('101', plain,
% 3.13/3.37      (![X0 : $i, X1 : $i]:
% 3.13/3.37         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 3.13/3.37      inference('sup+', [status(thm)], ['99', '100'])).
% 3.13/3.37  thf('102', plain,
% 3.13/3.37      (![X0 : $i]:
% 3.13/3.37         ((k3_tarski @ (k2_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0))
% 3.13/3.37           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.13/3.38      inference('demod', [status(thm)], ['96', '97', '98', '101'])).
% 3.13/3.38  thf('103', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.38      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.38  thf('104', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)) = (X0))),
% 3.13/3.38      inference('demod', [status(thm)], ['102', '103'])).
% 3.13/3.38  thf('105', plain,
% 3.13/3.38      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['89', '104'])).
% 3.13/3.38  thf('106', plain,
% 3.13/3.38      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 3.13/3.38      inference('demod', [status(thm)], ['77', '78'])).
% 3.13/3.38  thf('107', plain,
% 3.13/3.38      (![X31 : $i, X32 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 3.13/3.38           = (k5_xboole_0 @ X31 @ 
% 3.13/3.38              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 3.13/3.38      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.13/3.38  thf('108', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0))
% 3.13/3.38           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['106', '107'])).
% 3.13/3.38  thf('109', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.38      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.38  thf('110', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0))
% 3.13/3.38           = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 3.13/3.38      inference('demod', [status(thm)], ['108', '109'])).
% 3.13/3.38  thf('111', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['105', '110'])).
% 3.13/3.38  thf('112', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((X1) = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 3.13/3.38      inference('sup+', [status(thm)], ['88', '111'])).
% 3.13/3.38  thf('113', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)) = (X0))),
% 3.13/3.38      inference('demod', [status(thm)], ['87', '112'])).
% 3.13/3.38  thf('114', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         (((k3_tarski @ (k2_tarski @ sk_B @ X0)) = (X0))
% 3.13/3.38          | ((k3_tarski @ sk_B) = (sk_A)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['45', '113'])).
% 3.13/3.38  thf('115', plain,
% 3.13/3.38      ((((k1_tarski @ sk_A) = (sk_C_2)) | ((k3_tarski @ sk_B) = (sk_A)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['3', '114'])).
% 3.13/3.38  thf('116', plain,
% 3.13/3.38      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.38  thf('117', plain,
% 3.13/3.38      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 3.13/3.38         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('split', [status(esa)], ['116'])).
% 3.13/3.38  thf('118', plain,
% 3.13/3.38      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 3.13/3.38      inference('split', [status(esa)], ['116'])).
% 3.13/3.38  thf('119', plain,
% 3.13/3.38      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.38  thf('120', plain,
% 3.13/3.38      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('split', [status(esa)], ['119'])).
% 3.13/3.38  thf('121', plain,
% 3.13/3.38      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 3.13/3.38      inference('demod', [status(thm)], ['0', '1'])).
% 3.13/3.38  thf('122', plain,
% 3.13/3.38      (![X26 : $i, X27 : $i]:
% 3.13/3.38         (r1_tarski @ X26 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))),
% 3.13/3.38      inference('demod', [status(thm)], ['47', '48'])).
% 3.13/3.38  thf('123', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 3.13/3.38      inference('sup+', [status(thm)], ['121', '122'])).
% 3.13/3.38  thf('124', plain,
% 3.13/3.38      (![X61 : $i, X62 : $i]:
% 3.13/3.38         (((X62) = (k1_tarski @ X61))
% 3.13/3.38          | ((X62) = (k1_xboole_0))
% 3.13/3.38          | ~ (r1_tarski @ X62 @ (k1_tarski @ X61)))),
% 3.13/3.38      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 3.13/3.38  thf('125', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('sup-', [status(thm)], ['123', '124'])).
% 3.13/3.38  thf('126', plain,
% 3.13/3.38      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 3.13/3.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.38  thf('127', plain,
% 3.13/3.38      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('split', [status(esa)], ['126'])).
% 3.13/3.38  thf('128', plain,
% 3.13/3.38      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup-', [status(thm)], ['125', '127'])).
% 3.13/3.38  thf('129', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('simplify', [status(thm)], ['128'])).
% 3.13/3.38  thf('130', plain,
% 3.13/3.38      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 3.13/3.38      inference('split', [status(esa)], ['116'])).
% 3.13/3.38  thf('131', plain,
% 3.13/3.38      ((((sk_B) != (sk_B)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup-', [status(thm)], ['129', '130'])).
% 3.13/3.38  thf('132', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('simplify', [status(thm)], ['131'])).
% 3.13/3.38  thf('133', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('sat_resolution*', [status(thm)], ['118', '120', '132'])).
% 3.13/3.38  thf('134', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 3.13/3.38      inference('simpl_trail', [status(thm)], ['117', '133'])).
% 3.13/3.38  thf('135', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 3.13/3.38      inference('simplify_reflect-', [status(thm)], ['115', '134'])).
% 3.13/3.38  thf('136', plain,
% 3.13/3.38      (((k1_tarski @ (k3_tarski @ sk_B))
% 3.13/3.38         = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 3.13/3.38      inference('demod', [status(thm)], ['2', '135'])).
% 3.13/3.38  thf('137', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         (((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 3.13/3.38          | ((k3_xboole_0 @ sk_B @ X0) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('sup-', [status(thm)], ['8', '9'])).
% 3.13/3.38  thf('138', plain,
% 3.13/3.38      (![X14 : $i, X15 : $i]:
% 3.13/3.38         ((k4_xboole_0 @ X14 @ X15)
% 3.13/3.38           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.13/3.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.13/3.38  thf('139', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         (((k4_xboole_0 @ sk_B @ X0) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 3.13/3.38          | ((k3_xboole_0 @ sk_B @ X0) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['137', '138'])).
% 3.13/3.38  thf('140', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.38      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.38  thf('141', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 3.13/3.38          | ((k3_xboole_0 @ sk_B @ X0) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('demod', [status(thm)], ['139', '140'])).
% 3.13/3.38  thf('142', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 3.13/3.38      inference('simplify_reflect-', [status(thm)], ['115', '134'])).
% 3.13/3.38  thf('143', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 3.13/3.38          | ((k3_xboole_0 @ sk_B @ X0) = (k1_tarski @ (k3_tarski @ sk_B))))),
% 3.13/3.38      inference('demod', [status(thm)], ['141', '142'])).
% 3.13/3.38  thf('144', plain,
% 3.13/3.38      (![X31 : $i, X32 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 3.13/3.38           = (k5_xboole_0 @ X31 @ 
% 3.13/3.38              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 3.13/3.38      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.13/3.38  thf('145', plain,
% 3.13/3.38      (![X14 : $i, X15 : $i]:
% 3.13/3.38         ((k4_xboole_0 @ X14 @ X15)
% 3.13/3.38           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.13/3.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.13/3.38  thf('146', plain,
% 3.13/3.38      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 3.13/3.38           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 3.13/3.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.13/3.38  thf('147', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 3.13/3.38           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['145', '146'])).
% 3.13/3.38  thf('148', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 3.13/3.38           (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 3.13/3.38           = (k3_tarski @ (k2_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['144', '147'])).
% 3.13/3.38  thf('149', plain,
% 3.13/3.38      (![X18 : $i, X19 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ X18 @ (k3_xboole_0 @ X18 @ X19))) = (X18))),
% 3.13/3.38      inference('demod', [status(thm)], ['22', '23'])).
% 3.13/3.38  thf('150', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 3.13/3.38           (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (X1))),
% 3.13/3.38      inference('demod', [status(thm)], ['148', '149'])).
% 3.13/3.38  thf('151', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 3.13/3.38            (k3_xboole_0 @ sk_B @ (k1_tarski @ (k3_tarski @ sk_B)))) = (
% 3.13/3.38            sk_B))
% 3.13/3.38          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['143', '150'])).
% 3.13/3.38  thf('152', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 3.13/3.38      inference('sup+', [status(thm)], ['11', '14'])).
% 3.13/3.38  thf('153', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 3.13/3.38      inference('simplify_reflect-', [status(thm)], ['115', '134'])).
% 3.13/3.38  thf('154', plain,
% 3.13/3.38      (((k3_xboole_0 @ sk_B @ (k1_tarski @ (k3_tarski @ sk_B))) = (sk_B))),
% 3.13/3.38      inference('demod', [status(thm)], ['152', '153'])).
% 3.13/3.38  thf('155', plain,
% 3.13/3.38      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 3.13/3.38           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 3.13/3.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.13/3.38  thf('156', plain,
% 3.13/3.38      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['55', '56'])).
% 3.13/3.38  thf('157', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 3.13/3.38           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['155', '156'])).
% 3.13/3.38  thf('158', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.13/3.38      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.38  thf('159', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k1_xboole_0)
% 3.13/3.38           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 3.13/3.38      inference('demod', [status(thm)], ['157', '158'])).
% 3.13/3.38  thf('160', plain,
% 3.13/3.38      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['55', '56'])).
% 3.13/3.38  thf('161', plain,
% 3.13/3.38      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 3.13/3.38           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 3.13/3.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.13/3.38  thf('162', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 3.13/3.38           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['160', '161'])).
% 3.13/3.38  thf('163', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((X1) = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 3.13/3.38      inference('sup+', [status(thm)], ['88', '111'])).
% 3.13/3.38  thf('164', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 3.13/3.38      inference('demod', [status(thm)], ['162', '163'])).
% 3.13/3.38  thf('165', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 3.13/3.38           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['159', '164'])).
% 3.13/3.38  thf('166', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.38      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.38  thf('167', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 3.13/3.38      inference('demod', [status(thm)], ['165', '166'])).
% 3.13/3.38  thf('168', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 3.13/3.38      inference('demod', [status(thm)], ['162', '163'])).
% 3.13/3.38  thf('169', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['167', '168'])).
% 3.13/3.38  thf('170', plain,
% 3.13/3.38      (![X14 : $i, X15 : $i]:
% 3.13/3.38         ((k4_xboole_0 @ X14 @ X15)
% 3.13/3.38           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.13/3.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.13/3.38  thf('171', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 3.13/3.38      inference('demod', [status(thm)], ['162', '163'])).
% 3.13/3.38  thf('172', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k3_xboole_0 @ X1 @ X0)
% 3.13/3.38           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['170', '171'])).
% 3.13/3.38  thf('173', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         (((k3_xboole_0 @ sk_B @ X0) = (sk_B))
% 3.13/3.38          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 3.13/3.38      inference('demod', [status(thm)], ['151', '154', '169', '172'])).
% 3.13/3.38  thf('174', plain,
% 3.13/3.38      (![X31 : $i, X32 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 3.13/3.38           = (k5_xboole_0 @ X31 @ 
% 3.13/3.38              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 3.13/3.38      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.13/3.38  thf('175', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         (((k3_tarski @ (k2_tarski @ sk_B @ X0))
% 3.13/3.38            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ sk_B)))
% 3.13/3.38          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['173', '174'])).
% 3.13/3.38  thf('176', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 3.13/3.38      inference('demod', [status(thm)], ['165', '166'])).
% 3.13/3.38  thf('177', plain,
% 3.13/3.38      (![X0 : $i]:
% 3.13/3.38         (((k3_tarski @ (k2_tarski @ sk_B @ X0)) = (X0))
% 3.13/3.38          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 3.13/3.38      inference('demod', [status(thm)], ['175', '176'])).
% 3.13/3.38  thf('178', plain,
% 3.13/3.38      ((((k1_tarski @ (k3_tarski @ sk_B)) = (sk_C_2))
% 3.13/3.38        | ((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['136', '177'])).
% 3.13/3.38  thf('179', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 3.13/3.38      inference('simpl_trail', [status(thm)], ['117', '133'])).
% 3.13/3.38  thf('180', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 3.13/3.38      inference('simplify_reflect-', [status(thm)], ['115', '134'])).
% 3.13/3.38  thf('181', plain, (((sk_C_2) != (k1_tarski @ (k3_tarski @ sk_B)))),
% 3.13/3.38      inference('demod', [status(thm)], ['179', '180'])).
% 3.13/3.38  thf('182', plain, (((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B))),
% 3.13/3.38      inference('simplify_reflect-', [status(thm)], ['178', '181'])).
% 3.13/3.38  thf('183', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k3_xboole_0 @ X1 @ X0)
% 3.13/3.38           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['170', '171'])).
% 3.13/3.38  thf('184', plain,
% 3.13/3.38      (((k3_xboole_0 @ sk_B @ sk_C_2) = (k5_xboole_0 @ sk_B @ sk_B))),
% 3.13/3.38      inference('sup+', [status(thm)], ['182', '183'])).
% 3.13/3.38  thf('185', plain,
% 3.13/3.38      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['55', '56'])).
% 3.13/3.38  thf('186', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.13/3.38      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.38  thf('187', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 3.13/3.38      inference('demod', [status(thm)], ['184', '185', '186'])).
% 3.13/3.38  thf('188', plain,
% 3.13/3.38      (![X31 : $i, X32 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 3.13/3.38           = (k5_xboole_0 @ X31 @ 
% 3.13/3.38              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 3.13/3.38      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.13/3.38  thf('189', plain,
% 3.13/3.38      (((k3_tarski @ (k2_tarski @ sk_B @ sk_C_2))
% 3.13/3.38         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ k1_xboole_0)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['187', '188'])).
% 3.13/3.38  thf('190', plain,
% 3.13/3.38      (((k1_tarski @ (k3_tarski @ sk_B))
% 3.13/3.38         = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 3.13/3.38      inference('demod', [status(thm)], ['2', '135'])).
% 3.13/3.38  thf('191', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.38      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.38  thf('192', plain,
% 3.13/3.38      (((k1_tarski @ (k3_tarski @ sk_B)) = (k5_xboole_0 @ sk_B @ sk_C_2))),
% 3.13/3.38      inference('demod', [status(thm)], ['189', '190', '191'])).
% 3.13/3.38  thf('193', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['105', '110'])).
% 3.13/3.38  thf('194', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('sup-', [status(thm)], ['123', '124'])).
% 3.13/3.38  thf('195', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['36', '37'])).
% 3.13/3.38  thf('196', plain,
% 3.13/3.38      ((((k3_tarski @ sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['194', '195'])).
% 3.13/3.38  thf('197', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('sup-', [status(thm)], ['123', '124'])).
% 3.13/3.38  thf('198', plain,
% 3.13/3.38      ((((sk_B) = (k1_tarski @ (k3_tarski @ sk_B)))
% 3.13/3.38        | ((sk_B) = (k1_xboole_0))
% 3.13/3.38        | ((sk_B) = (k1_xboole_0)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['196', '197'])).
% 3.13/3.38  thf('199', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ (k3_tarski @ sk_B))))),
% 3.13/3.38      inference('simplify', [status(thm)], ['198'])).
% 3.13/3.38  thf('200', plain,
% 3.13/3.38      (((k1_tarski @ (k3_tarski @ sk_B)) = (k5_xboole_0 @ sk_B @ sk_C_2))),
% 3.13/3.38      inference('demod', [status(thm)], ['189', '190', '191'])).
% 3.13/3.38  thf('201', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 3.13/3.38      inference('demod', [status(thm)], ['165', '166'])).
% 3.13/3.38  thf('202', plain,
% 3.13/3.38      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ (k3_tarski @ sk_B))) = (sk_B))),
% 3.13/3.38      inference('sup+', [status(thm)], ['200', '201'])).
% 3.13/3.38  thf('203', plain,
% 3.13/3.38      ((((k5_xboole_0 @ sk_C_2 @ sk_B) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['199', '202'])).
% 3.13/3.38  thf('204', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['167', '168'])).
% 3.13/3.38  thf('205', plain,
% 3.13/3.38      ((((k5_xboole_0 @ sk_B @ sk_C_2) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 3.13/3.38      inference('demod', [status(thm)], ['203', '204'])).
% 3.13/3.38  thf('206', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i]:
% 3.13/3.38         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 3.13/3.38      inference('demod', [status(thm)], ['162', '163'])).
% 3.13/3.38  thf('207', plain,
% 3.13/3.38      ((((sk_C_2) = (k5_xboole_0 @ sk_B @ sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['205', '206'])).
% 3.13/3.38  thf('208', plain,
% 3.13/3.38      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['55', '56'])).
% 3.13/3.38  thf('209', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.13/3.38      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.38  thf('210', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 3.13/3.38      inference('demod', [status(thm)], ['207', '208', '209'])).
% 3.13/3.38  thf('211', plain,
% 3.13/3.38      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 3.13/3.38      inference('split', [status(esa)], ['126'])).
% 3.13/3.38  thf('212', plain,
% 3.13/3.38      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['55', '56'])).
% 3.13/3.38  thf('213', plain,
% 3.13/3.38      (![X14 : $i, X15 : $i]:
% 3.13/3.38         ((k4_xboole_0 @ X14 @ X15)
% 3.13/3.38           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.13/3.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.13/3.38  thf('214', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('simplify', [status(thm)], ['128'])).
% 3.13/3.38  thf('215', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 3.13/3.38      inference('cnf', [status(esa)], [t5_boole])).
% 3.13/3.38  thf('216', plain,
% 3.13/3.38      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B) = (X0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['214', '215'])).
% 3.13/3.38  thf('217', plain,
% 3.13/3.38      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 3.13/3.38           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 3.13/3.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.13/3.38  thf('218', plain,
% 3.13/3.38      ((![X0 : $i, X1 : $i]:
% 3.13/3.38          ((k5_xboole_0 @ X0 @ X1)
% 3.13/3.38            = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ X1))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['216', '217'])).
% 3.13/3.38  thf('219', plain,
% 3.13/3.38      ((![X0 : $i, X1 : $i]:
% 3.13/3.38          ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ sk_B @ X0))
% 3.13/3.38            = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ sk_B @ X0))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['213', '218'])).
% 3.13/3.38  thf('220', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('simplify', [status(thm)], ['128'])).
% 3.13/3.38  thf('221', plain,
% 3.13/3.38      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.13/3.38      inference('sup-', [status(thm)], ['72', '73'])).
% 3.13/3.38  thf('222', plain,
% 3.13/3.38      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['220', '221'])).
% 3.13/3.38  thf('223', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('simplify', [status(thm)], ['128'])).
% 3.13/3.38  thf('224', plain,
% 3.13/3.38      ((![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['222', '223'])).
% 3.13/3.38  thf('225', plain,
% 3.13/3.38      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B) = (X0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['214', '215'])).
% 3.13/3.38  thf('226', plain,
% 3.13/3.38      ((![X0 : $i, X1 : $i]:
% 3.13/3.38          ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ sk_B @ X0)) = (X1)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['219', '224', '225'])).
% 3.13/3.38  thf('227', plain,
% 3.13/3.38      ((![X0 : $i]:
% 3.13/3.38          ((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ (k3_xboole_0 @ sk_B @ X0))
% 3.13/3.38            = (k3_xboole_0 @ sk_B @ X0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['212', '226'])).
% 3.13/3.38  thf('228', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.13/3.38      inference('sup-', [status(thm)], ['50', '51'])).
% 3.13/3.38  thf('229', plain,
% 3.13/3.38      ((![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ X0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['227', '228'])).
% 3.13/3.38  thf('230', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('simplify', [status(thm)], ['128'])).
% 3.13/3.38  thf('231', plain,
% 3.13/3.38      ((![X0 : $i]: ((sk_B) = (k3_xboole_0 @ sk_B @ X0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['229', '230'])).
% 3.13/3.38  thf('232', plain,
% 3.13/3.38      (![X31 : $i, X32 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 3.13/3.38           = (k5_xboole_0 @ X31 @ 
% 3.13/3.38              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 3.13/3.38      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.13/3.38  thf('233', plain,
% 3.13/3.38      ((![X0 : $i]:
% 3.13/3.38          ((k3_tarski @ (k2_tarski @ sk_B @ X0))
% 3.13/3.38            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ sk_B))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['231', '232'])).
% 3.13/3.38  thf('234', plain,
% 3.13/3.38      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B) = (X0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['214', '215'])).
% 3.13/3.38  thf('235', plain,
% 3.13/3.38      ((![X0 : $i]:
% 3.13/3.38          ((k3_tarski @ (k2_tarski @ sk_B @ X0)) = (k5_xboole_0 @ sk_B @ X0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['233', '234'])).
% 3.13/3.38  thf('236', plain,
% 3.13/3.38      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 3.13/3.38      inference('demod', [status(thm)], ['0', '1'])).
% 3.13/3.38  thf('237', plain,
% 3.13/3.38      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_C_2)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['235', '236'])).
% 3.13/3.38  thf('238', plain,
% 3.13/3.38      (![X31 : $i, X32 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 3.13/3.38           = (k5_xboole_0 @ X31 @ 
% 3.13/3.38              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 3.13/3.38      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.13/3.38  thf('239', plain,
% 3.13/3.38      (![X31 : $i, X32 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ X31 @ X32))
% 3.13/3.38           = (k5_xboole_0 @ X31 @ 
% 3.13/3.38              (k5_xboole_0 @ X32 @ (k3_xboole_0 @ X31 @ X32))))),
% 3.13/3.38      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.13/3.38  thf('240', plain,
% 3.13/3.38      ((![X0 : $i, X1 : $i]:
% 3.13/3.38          ((k5_xboole_0 @ X0 @ X1)
% 3.13/3.38            = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ X1))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['216', '217'])).
% 3.13/3.38  thf('241', plain,
% 3.13/3.38      ((![X0 : $i]:
% 3.13/3.38          ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ sk_B))
% 3.13/3.38            = (k3_tarski @ (k2_tarski @ X0 @ sk_B))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['239', '240'])).
% 3.13/3.38  thf('242', plain,
% 3.13/3.38      (![X14 : $i, X15 : $i]:
% 3.13/3.38         ((k4_xboole_0 @ X14 @ X15)
% 3.13/3.38           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 3.13/3.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.13/3.38  thf('243', plain,
% 3.13/3.38      ((![X0 : $i]:
% 3.13/3.38          ((k4_xboole_0 @ X0 @ sk_B) = (k3_tarski @ (k2_tarski @ X0 @ sk_B))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['241', '242'])).
% 3.13/3.38  thf('244', plain,
% 3.13/3.38      (![X16 : $i, X17 : $i]:
% 3.13/3.38         ((k3_xboole_0 @ X16 @ (k3_tarski @ (k2_tarski @ X16 @ X17))) = (X16))),
% 3.13/3.38      inference('demod', [status(thm)], ['12', '13'])).
% 3.13/3.38  thf('245', plain,
% 3.13/3.38      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ sk_B)) = (X0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['243', '244'])).
% 3.13/3.38  thf('246', plain,
% 3.13/3.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.38         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 3.13/3.38           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 3.13/3.38      inference('sup+', [status(thm)], ['145', '146'])).
% 3.13/3.38  thf('247', plain,
% 3.13/3.38      ((![X0 : $i, X1 : $i]:
% 3.13/3.38          ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ sk_B)) @ X1)
% 3.13/3.38            = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['245', '246'])).
% 3.13/3.38  thf('248', plain,
% 3.13/3.38      ((![X0 : $i]:
% 3.13/3.38          ((k4_xboole_0 @ X0 @ sk_B) = (k3_tarski @ (k2_tarski @ X0 @ sk_B))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['241', '242'])).
% 3.13/3.38  thf(t46_xboole_1, axiom,
% 3.13/3.38    (![A:$i,B:$i]:
% 3.13/3.38     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 3.13/3.38  thf('249', plain,
% 3.13/3.38      (![X23 : $i, X24 : $i]:
% 3.13/3.38         ((k4_xboole_0 @ X23 @ (k2_xboole_0 @ X23 @ X24)) = (k1_xboole_0))),
% 3.13/3.38      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.13/3.38  thf('250', plain,
% 3.13/3.38      (![X64 : $i, X65 : $i]:
% 3.13/3.38         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 3.13/3.38      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.13/3.38  thf('251', plain,
% 3.13/3.38      (![X23 : $i, X24 : $i]:
% 3.13/3.38         ((k4_xboole_0 @ X23 @ (k3_tarski @ (k2_tarski @ X23 @ X24)))
% 3.13/3.38           = (k1_xboole_0))),
% 3.13/3.38      inference('demod', [status(thm)], ['249', '250'])).
% 3.13/3.38  thf('252', plain,
% 3.13/3.38      ((![X0 : $i]:
% 3.13/3.38          ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['248', '251'])).
% 3.13/3.38  thf('253', plain,
% 3.13/3.38      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('simplify', [status(thm)], ['128'])).
% 3.13/3.38  thf('254', plain,
% 3.13/3.38      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ sk_B)) = (sk_B)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['252', '253'])).
% 3.13/3.38  thf('255', plain,
% 3.13/3.38      ((![X0 : $i, X1 : $i]:
% 3.13/3.38          ((k5_xboole_0 @ sk_B @ X1)
% 3.13/3.38            = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['247', '254'])).
% 3.13/3.38  thf('256', plain,
% 3.13/3.38      ((![X0 : $i]:
% 3.13/3.38          ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ X0))
% 3.13/3.38            = (k3_tarski @ (k2_tarski @ X0 @ X0))))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('sup+', [status(thm)], ['238', '255'])).
% 3.13/3.38  thf('257', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['53', '54'])).
% 3.13/3.38  thf('258', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 3.13/3.38      inference('sup+', [status(thm)], ['21', '24'])).
% 3.13/3.38  thf('259', plain,
% 3.13/3.38      ((![X0 : $i]: ((k5_xboole_0 @ sk_B @ X0) = (X0)))
% 3.13/3.38         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['256', '257', '258'])).
% 3.13/3.38  thf('260', plain,
% 3.13/3.38      ((((k1_tarski @ sk_A) = (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 3.13/3.38      inference('demod', [status(thm)], ['237', '259'])).
% 3.13/3.38  thf('261', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 3.13/3.38      inference('simpl_trail', [status(thm)], ['117', '133'])).
% 3.13/3.38  thf('262', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('simplify_reflect-', [status(thm)], ['260', '261'])).
% 3.13/3.38  thf('263', plain,
% 3.13/3.38      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 3.13/3.38      inference('split', [status(esa)], ['126'])).
% 3.13/3.38  thf('264', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 3.13/3.38      inference('sat_resolution*', [status(thm)], ['262', '263'])).
% 3.13/3.38  thf('265', plain, (((sk_C_2) != (k1_xboole_0))),
% 3.13/3.38      inference('simpl_trail', [status(thm)], ['211', '264'])).
% 3.13/3.38  thf('266', plain, (((sk_B) = (k1_xboole_0))),
% 3.13/3.38      inference('simplify_reflect-', [status(thm)], ['210', '265'])).
% 3.13/3.38  thf('267', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ sk_B @ X0))),
% 3.13/3.38      inference('demod', [status(thm)], ['193', '266'])).
% 3.13/3.38  thf('268', plain, (((k1_tarski @ (k3_tarski @ sk_B)) = (sk_C_2))),
% 3.13/3.38      inference('demod', [status(thm)], ['192', '267'])).
% 3.13/3.38  thf('269', plain, (((sk_C_2) != (k1_tarski @ (k3_tarski @ sk_B)))),
% 3.13/3.38      inference('demod', [status(thm)], ['179', '180'])).
% 3.13/3.38  thf('270', plain, ($false),
% 3.13/3.38      inference('simplify_reflect-', [status(thm)], ['268', '269'])).
% 3.13/3.38  
% 3.13/3.38  % SZS output end Refutation
% 3.13/3.38  
% 3.13/3.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
