%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DrTglOLAIu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:37 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 325 expanded)
%              Number of leaves         :   27 ( 115 expanded)
%              Depth                    :   24
%              Number of atoms          :  832 (2333 expanded)
%              Number of equality atoms :   73 ( 249 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k5_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('9',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k5_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('12',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k5_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X9 @ ( k2_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
        = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','32'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('46',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X23 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('54',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k5_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('61',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36
        = ( k1_tarski @ X35 ) )
      | ( X36 = k1_xboole_0 )
      | ~ ( r1_tarski @ X36 @ ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('69',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['35','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','80'])).

thf('82',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','81'])).

thf('83',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('84',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('87',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['82','85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('91',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DrTglOLAIu
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:27:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.36/1.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.36/1.64  % Solved by: fo/fo7.sh
% 1.36/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.64  % done 1485 iterations in 1.164s
% 1.36/1.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.36/1.64  % SZS output start Refutation
% 1.36/1.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.36/1.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.36/1.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.36/1.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.36/1.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.36/1.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.36/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.36/1.64  thf(t58_zfmisc_1, conjecture,
% 1.36/1.64    (![A:$i,B:$i]:
% 1.36/1.64     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.36/1.64       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.36/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.64    (~( ![A:$i,B:$i]:
% 1.36/1.64        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.36/1.64          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 1.36/1.64    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 1.36/1.64  thf('0', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.36/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.64  thf(t3_boole, axiom,
% 1.36/1.64    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.36/1.64  thf('1', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.36/1.64      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.64  thf(t98_xboole_1, axiom,
% 1.36/1.64    (![A:$i,B:$i]:
% 1.36/1.64     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.36/1.64  thf('2', plain,
% 1.36/1.64      (![X32 : $i, X33 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X32 @ X33)
% 1.36/1.64           = (k5_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32)))),
% 1.36/1.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.36/1.64  thf('3', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['1', '2'])).
% 1.36/1.64  thf(t40_xboole_1, axiom,
% 1.36/1.64    (![A:$i,B:$i]:
% 1.36/1.64     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.36/1.64  thf('4', plain,
% 1.36/1.64      (![X16 : $i, X17 : $i]:
% 1.36/1.64         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.36/1.64           = (k4_xboole_0 @ X16 @ X17))),
% 1.36/1.64      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.36/1.64  thf('5', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0)
% 1.36/1.64           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['3', '4'])).
% 1.36/1.64  thf(t4_boole, axiom,
% 1.36/1.64    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.36/1.64  thf('6', plain,
% 1.36/1.64      (![X21 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X21) = (k1_xboole_0))),
% 1.36/1.64      inference('cnf', [status(esa)], [t4_boole])).
% 1.36/1.64  thf('7', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 1.36/1.64      inference('demod', [status(thm)], ['5', '6'])).
% 1.36/1.64  thf('8', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 1.36/1.64      inference('demod', [status(thm)], ['5', '6'])).
% 1.36/1.64  thf('9', plain,
% 1.36/1.64      (![X32 : $i, X33 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X32 @ X33)
% 1.36/1.64           = (k5_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32)))),
% 1.36/1.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.36/1.64  thf('10', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 1.36/1.64           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['8', '9'])).
% 1.36/1.64  thf('11', plain,
% 1.36/1.64      (![X21 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X21) = (k1_xboole_0))),
% 1.36/1.64      inference('cnf', [status(esa)], [t4_boole])).
% 1.36/1.64  thf('12', plain,
% 1.36/1.64      (![X32 : $i, X33 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X32 @ X33)
% 1.36/1.64           = (k5_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32)))),
% 1.36/1.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.36/1.64  thf('13', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['11', '12'])).
% 1.36/1.64  thf('14', plain,
% 1.36/1.64      (![X16 : $i, X17 : $i]:
% 1.36/1.64         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.36/1.64           = (k4_xboole_0 @ X16 @ X17))),
% 1.36/1.64      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.36/1.64  thf('15', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.36/1.64      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.64  thf('16', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['14', '15'])).
% 1.36/1.64  thf('17', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.36/1.64      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.64  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['16', '17'])).
% 1.36/1.64  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['13', '18'])).
% 1.36/1.64  thf('20', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 1.36/1.64      inference('demod', [status(thm)], ['10', '19'])).
% 1.36/1.64  thf(d10_xboole_0, axiom,
% 1.36/1.64    (![A:$i,B:$i]:
% 1.36/1.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.36/1.64  thf('21', plain,
% 1.36/1.64      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.36/1.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.64  thf('22', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.36/1.64      inference('simplify', [status(thm)], ['21'])).
% 1.36/1.64  thf(t10_xboole_1, axiom,
% 1.36/1.64    (![A:$i,B:$i,C:$i]:
% 1.36/1.64     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.36/1.64  thf('23', plain,
% 1.36/1.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.36/1.64         (~ (r1_tarski @ X9 @ X10)
% 1.36/1.64          | (r1_tarski @ X9 @ (k2_xboole_0 @ X11 @ X10)))),
% 1.36/1.64      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.36/1.64  thf('24', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['22', '23'])).
% 1.36/1.64  thf('25', plain,
% 1.36/1.64      (![X6 : $i, X8 : $i]:
% 1.36/1.64         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.36/1.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.64  thf('26', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.36/1.64          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 1.36/1.64      inference('sup-', [status(thm)], ['24', '25'])).
% 1.36/1.64  thf('27', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 1.36/1.64          | ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 1.36/1.64              = (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.36/1.64      inference('sup-', [status(thm)], ['20', '26'])).
% 1.36/1.64  thf('28', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['1', '2'])).
% 1.36/1.64  thf('29', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['22', '23'])).
% 1.36/1.64  thf('30', plain,
% 1.36/1.64      (![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['28', '29'])).
% 1.36/1.64  thf('31', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 1.36/1.64      inference('demod', [status(thm)], ['10', '19'])).
% 1.36/1.64  thf('32', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.36/1.64      inference('demod', [status(thm)], ['27', '30', '31'])).
% 1.36/1.64  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.36/1.64      inference('demod', [status(thm)], ['7', '32'])).
% 1.36/1.64  thf(t4_xboole_0, axiom,
% 1.36/1.64    (![A:$i,B:$i]:
% 1.36/1.64     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.36/1.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.36/1.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.36/1.64            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.36/1.64  thf('34', plain,
% 1.36/1.64      (![X2 : $i, X3 : $i]:
% 1.36/1.64         ((r1_xboole_0 @ X2 @ X3)
% 1.36/1.64          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 1.36/1.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.36/1.64  thf('35', plain,
% 1.36/1.64      (![X16 : $i, X17 : $i]:
% 1.36/1.64         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.36/1.64           = (k4_xboole_0 @ X16 @ X17))),
% 1.36/1.64      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.36/1.64  thf(t79_xboole_1, axiom,
% 1.36/1.64    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.36/1.64  thf('36', plain,
% 1.36/1.64      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 1.36/1.64      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.36/1.64  thf(symmetry_r1_xboole_0, axiom,
% 1.36/1.64    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.36/1.64  thf('37', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.36/1.64      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.36/1.64  thf('38', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['36', '37'])).
% 1.36/1.64  thf(t83_xboole_1, axiom,
% 1.36/1.64    (![A:$i,B:$i]:
% 1.36/1.64     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.36/1.64  thf('39', plain,
% 1.36/1.64      (![X29 : $i, X30 : $i]:
% 1.36/1.64         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 1.36/1.64      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.36/1.64  thf('40', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['38', '39'])).
% 1.36/1.64  thf(t49_xboole_1, axiom,
% 1.36/1.64    (![A:$i,B:$i,C:$i]:
% 1.36/1.64     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.36/1.64       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.36/1.64  thf('41', plain,
% 1.36/1.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.36/1.64         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 1.36/1.64           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 1.36/1.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.36/1.64  thf('42', plain,
% 1.36/1.64      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 1.36/1.64      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.36/1.64  thf('43', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.64         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 1.36/1.64      inference('sup+', [status(thm)], ['41', '42'])).
% 1.36/1.64  thf('44', plain,
% 1.36/1.64      (![X2 : $i, X3 : $i]:
% 1.36/1.64         ((r1_xboole_0 @ X2 @ X3)
% 1.36/1.64          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 1.36/1.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.36/1.64  thf(t16_xboole_1, axiom,
% 1.36/1.64    (![A:$i,B:$i,C:$i]:
% 1.36/1.64     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.36/1.64       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.36/1.64  thf('45', plain,
% 1.36/1.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.36/1.64         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 1.36/1.64           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.36/1.64      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.36/1.64  thf('46', plain,
% 1.36/1.64      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.36/1.64         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 1.36/1.64          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.36/1.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.36/1.64  thf('47', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.36/1.64         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 1.36/1.64          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['45', '46'])).
% 1.36/1.64  thf('48', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.64         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.36/1.64          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['44', '47'])).
% 1.36/1.64  thf('49', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.64         (r1_xboole_0 @ X2 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['43', '48'])).
% 1.36/1.64  thf(t66_xboole_1, axiom,
% 1.36/1.64    (![A:$i]:
% 1.36/1.64     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 1.36/1.64       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.36/1.64  thf('50', plain,
% 1.36/1.64      (![X23 : $i]: (((X23) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X23 @ X23))),
% 1.36/1.64      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.36/1.64  thf('51', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['49', '50'])).
% 1.36/1.64  thf('52', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['40', '51'])).
% 1.36/1.64  thf('53', plain,
% 1.36/1.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.36/1.64         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 1.36/1.64           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 1.36/1.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.36/1.64  thf('54', plain,
% 1.36/1.64      (![X32 : $i, X33 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X32 @ X33)
% 1.36/1.64           = (k5_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32)))),
% 1.36/1.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.36/1.64  thf('55', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.36/1.64           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.36/1.64      inference('sup+', [status(thm)], ['53', '54'])).
% 1.36/1.64  thf('56', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.36/1.64           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['52', '55'])).
% 1.36/1.64  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.36/1.64      inference('sup+', [status(thm)], ['13', '18'])).
% 1.36/1.64  thf('58', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.36/1.64      inference('demod', [status(thm)], ['56', '57'])).
% 1.36/1.64  thf('59', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['22', '23'])).
% 1.36/1.64  thf('60', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.36/1.64      inference('sup+', [status(thm)], ['58', '59'])).
% 1.36/1.64  thf(t39_zfmisc_1, axiom,
% 1.36/1.64    (![A:$i,B:$i]:
% 1.36/1.64     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.36/1.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.36/1.64  thf('61', plain,
% 1.36/1.64      (![X35 : $i, X36 : $i]:
% 1.36/1.64         (((X36) = (k1_tarski @ X35))
% 1.36/1.64          | ((X36) = (k1_xboole_0))
% 1.36/1.64          | ~ (r1_tarski @ X36 @ (k1_tarski @ X35)))),
% 1.36/1.64      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 1.36/1.64  thf('62', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 1.36/1.64          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.36/1.64      inference('sup-', [status(thm)], ['60', '61'])).
% 1.36/1.64  thf('63', plain,
% 1.36/1.64      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 1.36/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.64  thf('64', plain,
% 1.36/1.64      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 1.36/1.64        | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.36/1.64      inference('sup-', [status(thm)], ['62', '63'])).
% 1.36/1.64  thf('65', plain,
% 1.36/1.64      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.36/1.64      inference('simplify', [status(thm)], ['64'])).
% 1.36/1.64  thf('66', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.64         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.36/1.64          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['44', '47'])).
% 1.36/1.64  thf('67', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 1.36/1.64          | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.36/1.64      inference('sup-', [status(thm)], ['65', '66'])).
% 1.36/1.64  thf('68', plain,
% 1.36/1.64      (![X21 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X21) = (k1_xboole_0))),
% 1.36/1.64      inference('cnf', [status(esa)], [t4_boole])).
% 1.36/1.64  thf('69', plain,
% 1.36/1.64      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 1.36/1.64      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.36/1.64  thf('70', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.36/1.64      inference('sup+', [status(thm)], ['68', '69'])).
% 1.36/1.64  thf('71', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 1.36/1.64      inference('demod', [status(thm)], ['67', '70'])).
% 1.36/1.64  thf('72', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.36/1.64      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.36/1.64  thf('73', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_tarski @ sk_A))),
% 1.36/1.64      inference('sup-', [status(thm)], ['71', '72'])).
% 1.36/1.64  thf('74', plain,
% 1.36/1.64      (![X29 : $i, X30 : $i]:
% 1.36/1.64         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 1.36/1.64      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.36/1.64  thf('75', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_tarski @ sk_A))
% 1.36/1.64           = (k3_xboole_0 @ sk_B @ X0))),
% 1.36/1.64      inference('sup-', [status(thm)], ['73', '74'])).
% 1.36/1.64  thf('76', plain,
% 1.36/1.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.36/1.64         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 1.36/1.64           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 1.36/1.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.36/1.64  thf('77', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 1.36/1.64           = (k3_xboole_0 @ sk_B @ X0))),
% 1.36/1.64      inference('demod', [status(thm)], ['75', '76'])).
% 1.36/1.64  thf('78', plain,
% 1.36/1.64      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.36/1.64         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 1.36/1.64          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.36/1.64      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.36/1.64  thf('79', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_B @ X0))
% 1.36/1.64          | ~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 1.36/1.64      inference('sup-', [status(thm)], ['77', '78'])).
% 1.36/1.64  thf('80', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 1.36/1.64          | ~ (r2_hidden @ X1 @ 
% 1.36/1.64               (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))))),
% 1.36/1.64      inference('sup-', [status(thm)], ['35', '79'])).
% 1.36/1.64  thf('81', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 1.36/1.64          | ~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 1.36/1.64      inference('sup-', [status(thm)], ['34', '80'])).
% 1.36/1.64  thf('82', plain,
% 1.36/1.64      ((~ (r1_xboole_0 @ sk_B @ k1_xboole_0)
% 1.36/1.64        | (r1_xboole_0 @ sk_B @ 
% 1.36/1.64           (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 1.36/1.64      inference('sup-', [status(thm)], ['33', '81'])).
% 1.36/1.64  thf('83', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.36/1.64      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.64  thf('84', plain,
% 1.36/1.64      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 1.36/1.64      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.36/1.64  thf('85', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.36/1.64      inference('sup+', [status(thm)], ['83', '84'])).
% 1.36/1.64  thf('86', plain,
% 1.36/1.64      (![X0 : $i]:
% 1.36/1.64         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 1.36/1.64      inference('demod', [status(thm)], ['10', '19'])).
% 1.36/1.64  thf('87', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.36/1.64      inference('demod', [status(thm)], ['27', '30', '31'])).
% 1.36/1.64  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.36/1.64      inference('demod', [status(thm)], ['86', '87'])).
% 1.36/1.64  thf('89', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A))),
% 1.36/1.64      inference('demod', [status(thm)], ['82', '85', '88'])).
% 1.36/1.64  thf('90', plain,
% 1.36/1.64      (![X0 : $i, X1 : $i]:
% 1.36/1.64         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.36/1.64      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.36/1.64  thf('91', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.36/1.64      inference('sup-', [status(thm)], ['89', '90'])).
% 1.36/1.64  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 1.36/1.64  
% 1.36/1.64  % SZS output end Refutation
% 1.36/1.64  
% 1.47/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
