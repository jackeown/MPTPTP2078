%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KRQgpZ1ThG

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:02 EST 2020

% Result     : Theorem 13.78s
% Output     : Refutation 13.78s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 134 expanded)
%              Number of leaves         :   25 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  642 (1068 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t143_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
        & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
          & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
       => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( k2_zfmisc_1 @ X34 @ ( k2_xboole_0 @ X31 @ X33 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X31 ) @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('16',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('17',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ X28 )
      | ( r1_tarski @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','31'])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ),
    inference('sup+',[status(thm)],['2','36'])).

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X2 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ sk_C ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['1','49'])).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KRQgpZ1ThG
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 13.78/13.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.78/13.95  % Solved by: fo/fo7.sh
% 13.78/13.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.78/13.95  % done 14706 iterations in 13.501s
% 13.78/13.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.78/13.95  % SZS output start Refutation
% 13.78/13.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.78/13.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 13.78/13.95  thf(sk_D_type, type, sk_D: $i).
% 13.78/13.95  thf(sk_E_type, type, sk_E: $i).
% 13.78/13.95  thf(sk_C_type, type, sk_C: $i).
% 13.78/13.95  thf(sk_B_type, type, sk_B: $i).
% 13.78/13.95  thf(sk_A_type, type, sk_A: $i).
% 13.78/13.95  thf(sk_F_type, type, sk_F: $i).
% 13.78/13.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 13.78/13.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.78/13.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.78/13.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.78/13.95  thf(t143_zfmisc_1, conjecture,
% 13.78/13.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.78/13.95     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 13.78/13.95         ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 13.78/13.95       ( r1_tarski @
% 13.78/13.95         ( k2_xboole_0 @ A @ B ) @ 
% 13.78/13.95         ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ))).
% 13.78/13.95  thf(zf_stmt_0, negated_conjecture,
% 13.78/13.95    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.78/13.95        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 13.78/13.95            ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 13.78/13.95          ( r1_tarski @
% 13.78/13.95            ( k2_xboole_0 @ A @ B ) @ 
% 13.78/13.95            ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )),
% 13.78/13.95    inference('cnf.neg', [status(esa)], [t143_zfmisc_1])).
% 13.78/13.95  thf('0', plain,
% 13.78/13.95      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 13.78/13.95          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 13.78/13.95           (k2_xboole_0 @ sk_D @ sk_F)))),
% 13.78/13.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.78/13.95  thf(t120_zfmisc_1, axiom,
% 13.78/13.95    (![A:$i,B:$i,C:$i]:
% 13.78/13.95     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 13.78/13.95         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 13.78/13.95       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 13.78/13.95         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 13.78/13.95  thf('1', plain,
% 13.78/13.95      (![X31 : $i, X33 : $i, X34 : $i]:
% 13.78/13.95         ((k2_zfmisc_1 @ X34 @ (k2_xboole_0 @ X31 @ X33))
% 13.78/13.95           = (k2_xboole_0 @ (k2_zfmisc_1 @ X34 @ X31) @ 
% 13.78/13.95              (k2_zfmisc_1 @ X34 @ X33)))),
% 13.78/13.95      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 13.78/13.95  thf('2', plain,
% 13.78/13.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.78/13.95         ((k2_zfmisc_1 @ (k2_xboole_0 @ X31 @ X33) @ X32)
% 13.78/13.95           = (k2_xboole_0 @ (k2_zfmisc_1 @ X31 @ X32) @ 
% 13.78/13.95              (k2_zfmisc_1 @ X33 @ X32)))),
% 13.78/13.95      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 13.78/13.95  thf(d10_xboole_0, axiom,
% 13.78/13.95    (![A:$i,B:$i]:
% 13.78/13.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.78/13.95  thf('3', plain,
% 13.78/13.95      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 13.78/13.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.78/13.95  thf('4', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 13.78/13.95      inference('simplify', [status(thm)], ['3'])).
% 13.78/13.95  thf(t43_xboole_1, axiom,
% 13.78/13.95    (![A:$i,B:$i,C:$i]:
% 13.78/13.95     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 13.78/13.95       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 13.78/13.95  thf('5', plain,
% 13.78/13.95      (![X20 : $i, X21 : $i, X22 : $i]:
% 13.78/13.95         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 13.78/13.95          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 13.78/13.95      inference('cnf', [status(esa)], [t43_xboole_1])).
% 13.78/13.95  thf('6', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 13.78/13.95      inference('sup-', [status(thm)], ['4', '5'])).
% 13.78/13.95  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 13.78/13.95  thf('7', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 13.78/13.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 13.78/13.95  thf('8', plain,
% 13.78/13.95      (![X2 : $i, X4 : $i]:
% 13.78/13.95         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 13.78/13.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.78/13.95  thf('9', plain,
% 13.78/13.95      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 13.78/13.95      inference('sup-', [status(thm)], ['7', '8'])).
% 13.78/13.95  thf('10', plain,
% 13.78/13.95      (![X0 : $i]:
% 13.78/13.95         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['6', '9'])).
% 13.78/13.95  thf(t44_xboole_1, axiom,
% 13.78/13.95    (![A:$i,B:$i,C:$i]:
% 13.78/13.95     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 13.78/13.95       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 13.78/13.95  thf('11', plain,
% 13.78/13.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 13.78/13.95         ((r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 13.78/13.95          | ~ (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25))),
% 13.78/13.95      inference('cnf', [status(esa)], [t44_xboole_1])).
% 13.78/13.95  thf('12', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 13.78/13.95          | (r1_tarski @ (k2_xboole_0 @ X1 @ k1_xboole_0) @ 
% 13.78/13.95             (k2_xboole_0 @ X1 @ X0)))),
% 13.78/13.95      inference('sup-', [status(thm)], ['10', '11'])).
% 13.78/13.95  thf('13', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 13.78/13.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 13.78/13.95  thf('14', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         (r1_tarski @ (k2_xboole_0 @ X1 @ k1_xboole_0) @ 
% 13.78/13.95          (k2_xboole_0 @ X1 @ X0))),
% 13.78/13.95      inference('demod', [status(thm)], ['12', '13'])).
% 13.78/13.95  thf(t40_xboole_1, axiom,
% 13.78/13.95    (![A:$i,B:$i]:
% 13.78/13.95     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 13.78/13.95  thf('15', plain,
% 13.78/13.95      (![X18 : $i, X19 : $i]:
% 13.78/13.95         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 13.78/13.95           = (k4_xboole_0 @ X18 @ X19))),
% 13.78/13.95      inference('cnf', [status(esa)], [t40_xboole_1])).
% 13.78/13.95  thf('16', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 13.78/13.95      inference('simplify', [status(thm)], ['3'])).
% 13.78/13.95  thf('17', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 13.78/13.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 13.78/13.95  thf(t106_xboole_1, axiom,
% 13.78/13.95    (![A:$i,B:$i,C:$i]:
% 13.78/13.95     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 13.78/13.95       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 13.78/13.95  thf('18', plain,
% 13.78/13.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 13.78/13.95         ((r1_xboole_0 @ X5 @ X7)
% 13.78/13.95          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 13.78/13.95      inference('cnf', [status(esa)], [t106_xboole_1])).
% 13.78/13.95  thf('19', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 13.78/13.95      inference('sup-', [status(thm)], ['17', '18'])).
% 13.78/13.95  thf(symmetry_r1_xboole_0, axiom,
% 13.78/13.95    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 13.78/13.95  thf('20', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 13.78/13.95      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 13.78/13.95  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 13.78/13.95      inference('sup-', [status(thm)], ['19', '20'])).
% 13.78/13.95  thf(t86_xboole_1, axiom,
% 13.78/13.95    (![A:$i,B:$i,C:$i]:
% 13.78/13.95     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 13.78/13.95       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 13.78/13.95  thf('22', plain,
% 13.78/13.95      (![X26 : $i, X27 : $i, X28 : $i]:
% 13.78/13.95         (~ (r1_tarski @ X26 @ X27)
% 13.78/13.95          | ~ (r1_xboole_0 @ X26 @ X28)
% 13.78/13.95          | (r1_tarski @ X26 @ (k4_xboole_0 @ X27 @ X28)))),
% 13.78/13.95      inference('cnf', [status(esa)], [t86_xboole_1])).
% 13.78/13.95  thf('23', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         ((r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0))
% 13.78/13.95          | ~ (r1_tarski @ X0 @ X1))),
% 13.78/13.95      inference('sup-', [status(thm)], ['21', '22'])).
% 13.78/13.95  thf('24', plain,
% 13.78/13.95      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['16', '23'])).
% 13.78/13.95  thf(t36_xboole_1, axiom,
% 13.78/13.95    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 13.78/13.95  thf('25', plain,
% 13.78/13.95      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 13.78/13.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 13.78/13.95  thf('26', plain,
% 13.78/13.95      (![X2 : $i, X4 : $i]:
% 13.78/13.95         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 13.78/13.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.78/13.95  thf('27', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 13.78/13.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 13.78/13.95      inference('sup-', [status(thm)], ['25', '26'])).
% 13.78/13.95  thf('28', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['24', '27'])).
% 13.78/13.95  thf('29', plain,
% 13.78/13.95      (![X0 : $i]:
% 13.78/13.95         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 13.78/13.95      inference('sup+', [status(thm)], ['15', '28'])).
% 13.78/13.95  thf('30', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['24', '27'])).
% 13.78/13.95  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 13.78/13.95      inference('demod', [status(thm)], ['29', '30'])).
% 13.78/13.95  thf('32', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 13.78/13.95      inference('demod', [status(thm)], ['14', '31'])).
% 13.78/13.95  thf('33', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 13.78/13.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.78/13.95  thf(t1_xboole_1, axiom,
% 13.78/13.95    (![A:$i,B:$i,C:$i]:
% 13.78/13.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 13.78/13.95       ( r1_tarski @ A @ C ) ))).
% 13.78/13.95  thf('34', plain,
% 13.78/13.95      (![X12 : $i, X13 : $i, X14 : $i]:
% 13.78/13.95         (~ (r1_tarski @ X12 @ X13)
% 13.78/13.95          | ~ (r1_tarski @ X13 @ X14)
% 13.78/13.95          | (r1_tarski @ X12 @ X14))),
% 13.78/13.95      inference('cnf', [status(esa)], [t1_xboole_1])).
% 13.78/13.95  thf('35', plain,
% 13.78/13.95      (![X0 : $i]:
% 13.78/13.95         ((r1_tarski @ sk_B @ X0)
% 13.78/13.95          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['33', '34'])).
% 13.78/13.95  thf('36', plain,
% 13.78/13.95      (![X0 : $i]:
% 13.78/13.95         (r1_tarski @ sk_B @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['32', '35'])).
% 13.78/13.95  thf('37', plain,
% 13.78/13.95      (![X0 : $i]:
% 13.78/13.95         (r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F))),
% 13.78/13.95      inference('sup+', [status(thm)], ['2', '36'])).
% 13.78/13.95  thf('38', plain,
% 13.78/13.95      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.78/13.95         ((k2_zfmisc_1 @ (k2_xboole_0 @ X31 @ X33) @ X32)
% 13.78/13.95           = (k2_xboole_0 @ (k2_zfmisc_1 @ X31 @ X32) @ 
% 13.78/13.95              (k2_zfmisc_1 @ X33 @ X32)))),
% 13.78/13.95      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 13.78/13.95  thf('39', plain,
% 13.78/13.95      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 13.78/13.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 13.78/13.95  thf('40', plain,
% 13.78/13.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 13.78/13.95         ((r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 13.78/13.95          | ~ (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25))),
% 13.78/13.95      inference('cnf', [status(esa)], [t44_xboole_1])).
% 13.78/13.95  thf('41', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['39', '40'])).
% 13.78/13.95  thf('42', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 13.78/13.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.78/13.95  thf('43', plain,
% 13.78/13.95      (![X12 : $i, X13 : $i, X14 : $i]:
% 13.78/13.95         (~ (r1_tarski @ X12 @ X13)
% 13.78/13.95          | ~ (r1_tarski @ X13 @ X14)
% 13.78/13.95          | (r1_tarski @ X12 @ X14))),
% 13.78/13.95      inference('cnf', [status(esa)], [t1_xboole_1])).
% 13.78/13.95  thf('44', plain,
% 13.78/13.95      (![X0 : $i]:
% 13.78/13.95         ((r1_tarski @ sk_A @ X0)
% 13.78/13.95          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['42', '43'])).
% 13.78/13.95  thf('45', plain,
% 13.78/13.95      (![X0 : $i]:
% 13.78/13.95         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 13.78/13.95      inference('sup-', [status(thm)], ['41', '44'])).
% 13.78/13.95  thf('46', plain,
% 13.78/13.95      (![X0 : $i]:
% 13.78/13.95         (r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 13.78/13.95      inference('sup+', [status(thm)], ['38', '45'])).
% 13.78/13.95  thf(t13_xboole_1, axiom,
% 13.78/13.95    (![A:$i,B:$i,C:$i,D:$i]:
% 13.78/13.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 13.78/13.95       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 13.78/13.95  thf('47', plain,
% 13.78/13.95      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 13.78/13.95         (~ (r1_tarski @ X8 @ X9)
% 13.78/13.95          | ~ (r1_tarski @ X10 @ X11)
% 13.78/13.95          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ (k2_xboole_0 @ X9 @ X11)))),
% 13.78/13.95      inference('cnf', [status(esa)], [t13_xboole_1])).
% 13.78/13.95  thf('48', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.78/13.95         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X2) @ 
% 13.78/13.95           (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D) @ X1))
% 13.78/13.95          | ~ (r1_tarski @ X2 @ X1))),
% 13.78/13.95      inference('sup-', [status(thm)], ['46', '47'])).
% 13.78/13.95  thf('49', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 13.78/13.95          (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_C) @ sk_D) @ 
% 13.78/13.95           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F)))),
% 13.78/13.95      inference('sup-', [status(thm)], ['37', '48'])).
% 13.78/13.95  thf('50', plain,
% 13.78/13.95      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 13.78/13.95        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ sk_C) @ 
% 13.78/13.95         (k2_xboole_0 @ sk_D @ sk_F)))),
% 13.78/13.95      inference('sup+', [status(thm)], ['1', '49'])).
% 13.78/13.95  thf('51', plain,
% 13.78/13.95      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 13.78/13.95      inference('cnf', [status(esa)], [t36_xboole_1])).
% 13.78/13.95  thf('52', plain,
% 13.78/13.95      (![X18 : $i, X19 : $i]:
% 13.78/13.95         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 13.78/13.95           = (k4_xboole_0 @ X18 @ X19))),
% 13.78/13.95      inference('cnf', [status(esa)], [t40_xboole_1])).
% 13.78/13.95  thf('53', plain,
% 13.78/13.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 13.78/13.95         ((r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25))
% 13.78/13.95          | ~ (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25))),
% 13.78/13.95      inference('cnf', [status(esa)], [t44_xboole_1])).
% 13.78/13.95  thf('54', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.78/13.95         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 13.78/13.95          | (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 13.78/13.95      inference('sup-', [status(thm)], ['52', '53'])).
% 13.78/13.95  thf('55', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['51', '54'])).
% 13.78/13.95  thf('56', plain,
% 13.78/13.95      (![X2 : $i, X4 : $i]:
% 13.78/13.95         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 13.78/13.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.78/13.95  thf('57', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 13.78/13.95          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 13.78/13.95      inference('sup-', [status(thm)], ['55', '56'])).
% 13.78/13.95  thf('58', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]:
% 13.78/13.95         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 13.78/13.95      inference('sup-', [status(thm)], ['51', '54'])).
% 13.78/13.95  thf('59', plain,
% 13.78/13.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 13.78/13.95      inference('demod', [status(thm)], ['57', '58'])).
% 13.78/13.95  thf('60', plain,
% 13.78/13.95      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 13.78/13.95        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 13.78/13.95         (k2_xboole_0 @ sk_D @ sk_F)))),
% 13.78/13.95      inference('demod', [status(thm)], ['50', '59'])).
% 13.78/13.95  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 13.78/13.95  
% 13.78/13.95  % SZS output end Refutation
% 13.78/13.95  
% 13.78/13.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
