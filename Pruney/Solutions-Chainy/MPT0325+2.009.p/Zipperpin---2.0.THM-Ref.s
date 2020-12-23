%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gaAHRPNPSK

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:41 EST 2020

% Result     : Theorem 2.74s
% Output     : Refutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 303 expanded)
%              Number of leaves         :   34 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          : 1179 (2649 expanded)
%              Number of equality atoms :   86 ( 209 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X40 @ X41 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X40 @ X42 ) @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('19',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X43 @ X45 ) @ ( k3_xboole_0 @ X44 @ X46 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('20',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r1_tarski @ X38 @ X39 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X37 @ X38 ) @ ( k2_zfmisc_1 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X40 @ X41 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X40 @ X42 ) @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X43 @ X45 ) @ ( k3_xboole_0 @ X44 @ X46 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
    = ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46','49','50'])).

thf('52',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['30','51'])).

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r1_tarski @ X38 @ X39 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X38 @ X37 ) @ ( k2_zfmisc_1 @ X39 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
        | ( r1_tarski @ sk_A @ X0 )
        | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('58',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('62',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('65',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X33 @ X30 @ X31 ) @ ( sk_E_1 @ X33 @ X30 @ X31 ) @ X33 @ X30 @ X31 )
      | ( X32
       != ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('67',plain,(
    ! [X30: $i,X31: $i,X33: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X33 @ X30 @ X31 ) @ ( sk_E_1 @ X33 @ X30 @ X31 ) @ X33 @ X30 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ X24 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('72',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('75',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('80',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X40 @ X41 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X40 @ X42 ) @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('88',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X43 @ X45 ) @ ( k3_xboole_0 @ X44 @ X46 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) )
      | ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','96'])).

thf('98',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( r1_tarski @ X38 @ X39 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X38 @ X37 ) @ ( k2_zfmisc_1 @ X39 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('99',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('101',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','103'])).

thf('105',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D_1 )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('107',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['105','106'])).

thf('108',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['64','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('110',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X21 @ X25 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','108','113'])).

thf('115',plain,(
    $false ),
    inference(simplify,[status(thm)],['114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gaAHRPNPSK
% 0.13/0.36  % Computer   : n020.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:43:37 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 2.74/2.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.74/2.94  % Solved by: fo/fo7.sh
% 2.74/2.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.74/2.94  % done 4638 iterations in 2.465s
% 2.74/2.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.74/2.94  % SZS output start Refutation
% 2.74/2.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.74/2.94  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.74/2.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.74/2.94  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.74/2.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 2.74/2.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.74/2.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.74/2.94  thf(sk_A_type, type, sk_A: $i).
% 2.74/2.94  thf(sk_B_type, type, sk_B: $i > $i).
% 2.74/2.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.74/2.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.74/2.94  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 2.74/2.94  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.74/2.94  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 2.74/2.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.74/2.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.74/2.94  thf(t138_zfmisc_1, conjecture,
% 2.74/2.94    (![A:$i,B:$i,C:$i,D:$i]:
% 2.74/2.94     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.74/2.94       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 2.74/2.94         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 2.74/2.94  thf(zf_stmt_0, negated_conjecture,
% 2.74/2.94    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.74/2.94        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.74/2.94          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 2.74/2.94            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 2.74/2.94    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 2.74/2.94  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 2.74/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.94  thf(d10_xboole_0, axiom,
% 2.74/2.94    (![A:$i,B:$i]:
% 2.74/2.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.74/2.94  thf('1', plain,
% 2.74/2.94      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 2.74/2.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.74/2.94  thf('2', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.74/2.94      inference('simplify', [status(thm)], ['1'])).
% 2.74/2.94  thf(commutativity_k3_xboole_0, axiom,
% 2.74/2.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.74/2.94  thf('3', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.74/2.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.74/2.94  thf(t48_xboole_1, axiom,
% 2.74/2.94    (![A:$i,B:$i]:
% 2.74/2.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.74/2.94  thf('4', plain,
% 2.74/2.94      (![X18 : $i, X19 : $i]:
% 2.74/2.94         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.74/2.94           = (k3_xboole_0 @ X18 @ X19))),
% 2.74/2.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.74/2.94  thf(t106_xboole_1, axiom,
% 2.74/2.94    (![A:$i,B:$i,C:$i]:
% 2.74/2.94     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.74/2.94       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 2.74/2.94  thf('5', plain,
% 2.74/2.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.74/2.94         ((r1_tarski @ X13 @ X14)
% 2.74/2.94          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.74/2.94  thf('6', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['4', '5'])).
% 2.74/2.94  thf('7', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['3', '6'])).
% 2.74/2.94  thf('8', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.74/2.94      inference('sup-', [status(thm)], ['2', '7'])).
% 2.74/2.94  thf(t118_zfmisc_1, axiom,
% 2.74/2.94    (![A:$i,B:$i,C:$i]:
% 2.74/2.94     ( ( r1_tarski @ A @ B ) =>
% 2.74/2.94       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 2.74/2.94         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 2.74/2.94  thf('9', plain,
% 2.74/2.94      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X40 @ X41)
% 2.74/2.94          | (r1_tarski @ (k2_zfmisc_1 @ X40 @ X42) @ (k2_zfmisc_1 @ X41 @ X42)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 2.74/2.94  thf('10', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.94         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 2.74/2.94          (k2_zfmisc_1 @ X0 @ X2))),
% 2.74/2.94      inference('sup-', [status(thm)], ['8', '9'])).
% 2.74/2.94  thf('11', plain,
% 2.74/2.94      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 2.74/2.94        (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.74/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.94  thf(l32_xboole_1, axiom,
% 2.74/2.94    (![A:$i,B:$i]:
% 2.74/2.94     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.74/2.94  thf('12', plain,
% 2.74/2.94      (![X10 : $i, X12 : $i]:
% 2.74/2.94         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 2.74/2.94          | ~ (r1_tarski @ X10 @ X12))),
% 2.74/2.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.74/2.94  thf('13', plain,
% 2.74/2.94      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 2.74/2.94         (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)) = (k1_xboole_0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['11', '12'])).
% 2.74/2.94  thf('14', plain,
% 2.74/2.94      (![X18 : $i, X19 : $i]:
% 2.74/2.94         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.74/2.94           = (k3_xboole_0 @ X18 @ X19))),
% 2.74/2.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.74/2.94  thf('15', plain,
% 2.74/2.94      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 2.74/2.94         = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 2.74/2.94            (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)))),
% 2.74/2.94      inference('sup+', [status(thm)], ['13', '14'])).
% 2.74/2.94  thf(t3_boole, axiom,
% 2.74/2.94    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.74/2.94  thf('16', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 2.74/2.94      inference('cnf', [status(esa)], [t3_boole])).
% 2.74/2.94  thf('17', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.74/2.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.74/2.94  thf('18', plain,
% 2.74/2.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1)
% 2.74/2.94         = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.74/2.94            (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.74/2.94      inference('demod', [status(thm)], ['15', '16', '17'])).
% 2.74/2.94  thf(t123_zfmisc_1, axiom,
% 2.74/2.94    (![A:$i,B:$i,C:$i,D:$i]:
% 2.74/2.94     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 2.74/2.94       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 2.74/2.94  thf('19', plain,
% 2.74/2.94      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.74/2.94         ((k2_zfmisc_1 @ (k3_xboole_0 @ X43 @ X45) @ (k3_xboole_0 @ X44 @ X46))
% 2.74/2.94           = (k3_xboole_0 @ (k2_zfmisc_1 @ X43 @ X44) @ 
% 2.74/2.94              (k2_zfmisc_1 @ X45 @ X46)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.74/2.94  thf('20', plain,
% 2.74/2.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1)
% 2.74/2.94         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 2.74/2.94            (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.74/2.94      inference('demod', [status(thm)], ['18', '19'])).
% 2.74/2.94  thf(t117_zfmisc_1, axiom,
% 2.74/2.94    (![A:$i,B:$i,C:$i]:
% 2.74/2.94     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.74/2.94          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 2.74/2.94            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 2.74/2.94          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 2.74/2.94  thf('21', plain,
% 2.74/2.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.74/2.94         (((X37) = (k1_xboole_0))
% 2.74/2.94          | (r1_tarski @ X38 @ X39)
% 2.74/2.94          | ~ (r1_tarski @ (k2_zfmisc_1 @ X37 @ X38) @ 
% 2.74/2.94               (k2_zfmisc_1 @ X37 @ X39)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.74/2.94  thf('22', plain,
% 2.74/2.94      (![X0 : $i]:
% 2.74/2.94         (~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ X0) @ 
% 2.74/2.94             (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.74/2.94          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.74/2.94          | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['20', '21'])).
% 2.74/2.94  thf('23', plain,
% 2.74/2.94      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 2.74/2.94        | (r1_tarski @ sk_B_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['10', '22'])).
% 2.74/2.94  thf('24', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['4', '5'])).
% 2.74/2.94  thf('25', plain,
% 2.74/2.94      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 2.74/2.94        | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['23', '24'])).
% 2.74/2.94  thf('26', plain,
% 2.74/2.94      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B_1 @ sk_D_1))),
% 2.74/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.94  thf('27', plain,
% 2.74/2.94      ((~ (r1_tarski @ sk_B_1 @ sk_D_1)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('split', [status(esa)], ['26'])).
% 2.74/2.94  thf('28', plain,
% 2.74/2.94      ((((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0)))
% 2.74/2.94         <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['25', '27'])).
% 2.74/2.94  thf('29', plain,
% 2.74/2.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1)
% 2.74/2.94         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 2.74/2.94            (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.74/2.94      inference('demod', [status(thm)], ['18', '19'])).
% 2.74/2.94  thf('30', plain,
% 2.74/2.94      ((((k2_zfmisc_1 @ sk_A @ sk_B_1)
% 2.74/2.94          = (k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))))
% 2.74/2.94         <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('sup+', [status(thm)], ['28', '29'])).
% 2.74/2.94  thf(t4_boole, axiom,
% 2.74/2.94    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.74/2.94  thf('31', plain,
% 2.74/2.94      (![X20 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 2.74/2.94      inference('cnf', [status(esa)], [t4_boole])).
% 2.74/2.94  thf('32', plain,
% 2.74/2.94      (![X10 : $i, X11 : $i]:
% 2.74/2.94         ((r1_tarski @ X10 @ X11)
% 2.74/2.94          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 2.74/2.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.74/2.94  thf('33', plain,
% 2.74/2.94      (![X0 : $i]:
% 2.74/2.94         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['31', '32'])).
% 2.74/2.94  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.74/2.94      inference('simplify', [status(thm)], ['33'])).
% 2.74/2.94  thf('35', plain,
% 2.74/2.94      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X40 @ X41)
% 2.74/2.94          | (r1_tarski @ (k2_zfmisc_1 @ X40 @ X42) @ (k2_zfmisc_1 @ X41 @ X42)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 2.74/2.94  thf('36', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]:
% 2.74/2.94         (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ 
% 2.74/2.94          (k2_zfmisc_1 @ X0 @ X1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['34', '35'])).
% 2.74/2.94  thf('37', plain,
% 2.74/2.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1)
% 2.74/2.94         = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.74/2.94            (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.74/2.94      inference('demod', [status(thm)], ['15', '16', '17'])).
% 2.74/2.94  thf('38', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['4', '5'])).
% 2.74/2.94  thf('39', plain,
% 2.74/2.94      (![X0 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.74/2.94          | (r1_tarski @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['37', '38'])).
% 2.74/2.94  thf('40', plain,
% 2.74/2.94      ((r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 2.74/2.94        (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['36', '39'])).
% 2.74/2.94  thf('41', plain,
% 2.74/2.94      (![X10 : $i, X12 : $i]:
% 2.74/2.94         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 2.74/2.94          | ~ (r1_tarski @ X10 @ X12))),
% 2.74/2.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.74/2.94  thf('42', plain,
% 2.74/2.94      (((k4_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 2.74/2.94         (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)) = (k1_xboole_0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['40', '41'])).
% 2.74/2.94  thf('43', plain,
% 2.74/2.94      (![X18 : $i, X19 : $i]:
% 2.74/2.94         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.74/2.94           = (k3_xboole_0 @ X18 @ X19))),
% 2.74/2.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.74/2.94  thf('44', plain,
% 2.74/2.94      (((k4_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ k1_xboole_0)
% 2.74/2.94         = (k3_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 2.74/2.94            (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)))),
% 2.74/2.94      inference('sup+', [status(thm)], ['42', '43'])).
% 2.74/2.94  thf('45', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 2.74/2.94      inference('cnf', [status(esa)], [t3_boole])).
% 2.74/2.94  thf('46', plain,
% 2.74/2.94      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.74/2.94         ((k2_zfmisc_1 @ (k3_xboole_0 @ X43 @ X45) @ (k3_xboole_0 @ X44 @ X46))
% 2.74/2.94           = (k3_xboole_0 @ (k2_zfmisc_1 @ X43 @ X44) @ 
% 2.74/2.94              (k2_zfmisc_1 @ X45 @ X46)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.74/2.94  thf('47', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.74/2.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.74/2.94  thf(t2_boole, axiom,
% 2.74/2.94    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.74/2.94  thf('48', plain,
% 2.74/2.94      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 2.74/2.94      inference('cnf', [status(esa)], [t2_boole])).
% 2.74/2.94  thf('49', plain,
% 2.74/2.94      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.74/2.94      inference('sup+', [status(thm)], ['47', '48'])).
% 2.74/2.94  thf('50', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.74/2.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.74/2.94  thf('51', plain,
% 2.74/2.94      (((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)
% 2.74/2.94         = (k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.74/2.94      inference('demod', [status(thm)], ['44', '45', '46', '49', '50'])).
% 2.74/2.94  thf('52', plain,
% 2.74/2.94      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) = (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 2.74/2.94         <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('sup+', [status(thm)], ['30', '51'])).
% 2.74/2.94  thf('53', plain,
% 2.74/2.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.74/2.94         (((X37) = (k1_xboole_0))
% 2.74/2.94          | (r1_tarski @ X38 @ X39)
% 2.74/2.94          | ~ (r1_tarski @ (k2_zfmisc_1 @ X38 @ X37) @ 
% 2.74/2.94               (k2_zfmisc_1 @ X39 @ X37)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.74/2.94  thf('54', plain,
% 2.74/2.94      ((![X0 : $i]:
% 2.74/2.94          (~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ 
% 2.74/2.94              (k2_zfmisc_1 @ X0 @ sk_B_1))
% 2.74/2.94           | (r1_tarski @ sk_A @ X0)
% 2.74/2.94           | ((sk_B_1) = (k1_xboole_0))))
% 2.74/2.94         <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['52', '53'])).
% 2.74/2.94  thf('55', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]:
% 2.74/2.94         (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ 
% 2.74/2.94          (k2_zfmisc_1 @ X0 @ X1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['34', '35'])).
% 2.74/2.94  thf('56', plain,
% 2.74/2.94      ((![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_B_1) = (k1_xboole_0))))
% 2.74/2.94         <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('demod', [status(thm)], ['54', '55'])).
% 2.74/2.94  thf('57', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.74/2.94      inference('simplify', [status(thm)], ['33'])).
% 2.74/2.94  thf('58', plain,
% 2.74/2.94      (![X7 : $i, X9 : $i]:
% 2.74/2.94         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.74/2.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.74/2.94  thf('59', plain,
% 2.74/2.94      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['57', '58'])).
% 2.74/2.94  thf('60', plain,
% 2.74/2.94      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 2.74/2.94         <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['56', '59'])).
% 2.74/2.94  thf('61', plain,
% 2.74/2.94      ((~ (r1_tarski @ sk_B_1 @ sk_D_1)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('split', [status(esa)], ['26'])).
% 2.74/2.94  thf('62', plain,
% 2.74/2.94      (((~ (r1_tarski @ k1_xboole_0 @ sk_D_1) | ((sk_A) = (k1_xboole_0))))
% 2.74/2.94         <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['60', '61'])).
% 2.74/2.94  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.74/2.94      inference('simplify', [status(thm)], ['33'])).
% 2.74/2.94  thf('64', plain,
% 2.74/2.94      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 2.74/2.94      inference('demod', [status(thm)], ['62', '63'])).
% 2.74/2.94  thf(t7_xboole_0, axiom,
% 2.74/2.94    (![A:$i]:
% 2.74/2.94     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.74/2.94          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.74/2.94  thf('65', plain,
% 2.74/2.94      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 2.74/2.94      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.74/2.94  thf(d2_zfmisc_1, axiom,
% 2.74/2.94    (![A:$i,B:$i,C:$i]:
% 2.74/2.94     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.74/2.94       ( ![D:$i]:
% 2.74/2.94         ( ( r2_hidden @ D @ C ) <=>
% 2.74/2.94           ( ?[E:$i,F:$i]:
% 2.74/2.94             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 2.74/2.94               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 2.74/2.94  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 2.74/2.94  thf(zf_stmt_2, axiom,
% 2.74/2.94    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 2.74/2.94     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 2.74/2.94       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 2.74/2.94         ( r2_hidden @ E @ A ) ) ))).
% 2.74/2.94  thf(zf_stmt_3, axiom,
% 2.74/2.94    (![A:$i,B:$i,C:$i]:
% 2.74/2.94     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 2.74/2.94       ( ![D:$i]:
% 2.74/2.94         ( ( r2_hidden @ D @ C ) <=>
% 2.74/2.94           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 2.74/2.94  thf('66', plain,
% 2.74/2.94      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.74/2.94         (~ (r2_hidden @ X33 @ X32)
% 2.74/2.94          | (zip_tseitin_0 @ (sk_F_1 @ X33 @ X30 @ X31) @ 
% 2.74/2.94             (sk_E_1 @ X33 @ X30 @ X31) @ X33 @ X30 @ X31)
% 2.74/2.94          | ((X32) != (k2_zfmisc_1 @ X31 @ X30)))),
% 2.74/2.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.74/2.94  thf('67', plain,
% 2.74/2.94      (![X30 : $i, X31 : $i, X33 : $i]:
% 2.74/2.94         ((zip_tseitin_0 @ (sk_F_1 @ X33 @ X30 @ X31) @ 
% 2.74/2.94           (sk_E_1 @ X33 @ X30 @ X31) @ X33 @ X30 @ X31)
% 2.74/2.94          | ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X31 @ X30)))),
% 2.74/2.94      inference('simplify', [status(thm)], ['66'])).
% 2.74/2.94  thf('68', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]:
% 2.74/2.94         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.74/2.94          | (zip_tseitin_0 @ 
% 2.74/2.94             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.74/2.94             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.74/2.94             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['65', '67'])).
% 2.74/2.94  thf('69', plain,
% 2.74/2.94      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.74/2.94         ((r2_hidden @ X22 @ X24)
% 2.74/2.94          | ~ (zip_tseitin_0 @ X22 @ X21 @ X23 @ X24 @ X25))),
% 2.74/2.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.74/2.94  thf('70', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]:
% 2.74/2.94         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 2.74/2.94          | (r2_hidden @ 
% 2.74/2.94             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['68', '69'])).
% 2.74/2.94  thf('71', plain,
% 2.74/2.94      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.74/2.94      inference('sup+', [status(thm)], ['47', '48'])).
% 2.74/2.94  thf(t4_xboole_0, axiom,
% 2.74/2.94    (![A:$i,B:$i]:
% 2.74/2.94     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.74/2.94            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.74/2.94       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.74/2.94            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.74/2.94  thf('72', plain,
% 2.74/2.94      (![X2 : $i, X4 : $i, X5 : $i]:
% 2.74/2.94         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 2.74/2.94          | ~ (r1_xboole_0 @ X2 @ X5))),
% 2.74/2.94      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.74/2.94  thf('73', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]:
% 2.74/2.94         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['71', '72'])).
% 2.74/2.94  thf('74', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.74/2.94      inference('simplify', [status(thm)], ['33'])).
% 2.74/2.94  thf('75', plain,
% 2.74/2.94      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.74/2.94         ((r1_xboole_0 @ X13 @ X15)
% 2.74/2.94          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.74/2.94  thf('76', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.74/2.94      inference('sup-', [status(thm)], ['74', '75'])).
% 2.74/2.94  thf('77', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.74/2.94      inference('demod', [status(thm)], ['73', '76'])).
% 2.74/2.94  thf('78', plain,
% 2.74/2.94      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['70', '77'])).
% 2.74/2.94  thf('79', plain,
% 2.74/2.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1)
% 2.74/2.94         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 2.74/2.94            (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.74/2.94      inference('demod', [status(thm)], ['18', '19'])).
% 2.74/2.94  thf('80', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.74/2.94      inference('simplify', [status(thm)], ['1'])).
% 2.74/2.94  thf('81', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['4', '5'])).
% 2.74/2.94  thf('82', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.74/2.94      inference('sup-', [status(thm)], ['80', '81'])).
% 2.74/2.94  thf('83', plain,
% 2.74/2.94      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X40 @ X41)
% 2.74/2.94          | (r1_tarski @ (k2_zfmisc_1 @ X40 @ X42) @ (k2_zfmisc_1 @ X41 @ X42)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 2.74/2.94  thf('84', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.94         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 2.74/2.94          (k2_zfmisc_1 @ X0 @ X2))),
% 2.74/2.94      inference('sup-', [status(thm)], ['82', '83'])).
% 2.74/2.94  thf('85', plain,
% 2.74/2.94      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 2.74/2.94        (k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.74/2.94      inference('sup+', [status(thm)], ['79', '84'])).
% 2.74/2.94  thf('86', plain,
% 2.74/2.94      (![X18 : $i, X19 : $i]:
% 2.74/2.94         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.74/2.94           = (k3_xboole_0 @ X18 @ X19))),
% 2.74/2.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.74/2.94  thf('87', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.74/2.94      inference('simplify', [status(thm)], ['1'])).
% 2.74/2.94  thf('88', plain,
% 2.74/2.94      (![X10 : $i, X12 : $i]:
% 2.74/2.94         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 2.74/2.94          | ~ (r1_tarski @ X10 @ X12))),
% 2.74/2.94      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.74/2.94  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['87', '88'])).
% 2.74/2.94  thf('90', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 2.74/2.94      inference('cnf', [status(esa)], [t3_boole])).
% 2.74/2.94  thf('91', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]:
% 2.74/2.94         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 2.74/2.94      inference('sup+', [status(thm)], ['89', '90'])).
% 2.74/2.94  thf('92', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.74/2.94      inference('sup+', [status(thm)], ['86', '91'])).
% 2.74/2.94  thf('93', plain,
% 2.74/2.94      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.74/2.94         ((k2_zfmisc_1 @ (k3_xboole_0 @ X43 @ X45) @ (k3_xboole_0 @ X44 @ X46))
% 2.74/2.94           = (k3_xboole_0 @ (k2_zfmisc_1 @ X43 @ X44) @ 
% 2.74/2.94              (k2_zfmisc_1 @ X45 @ X46)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.74/2.94  thf('94', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['3', '6'])).
% 2.74/2.94  thf('95', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X4 @ 
% 2.74/2.94             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 2.74/2.94          | (r1_tarski @ X4 @ (k2_zfmisc_1 @ X2 @ X0)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['93', '94'])).
% 2.74/2.94  thf('96', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.74/2.94         (~ (r1_tarski @ X3 @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1)))
% 2.74/2.94          | (r1_tarski @ X3 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['92', '95'])).
% 2.74/2.94  thf('97', plain,
% 2.74/2.94      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 2.74/2.94        (k2_zfmisc_1 @ sk_C_1 @ sk_B_1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['85', '96'])).
% 2.74/2.94  thf('98', plain,
% 2.74/2.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.74/2.94         (((X37) = (k1_xboole_0))
% 2.74/2.94          | (r1_tarski @ X38 @ X39)
% 2.74/2.94          | ~ (r1_tarski @ (k2_zfmisc_1 @ X38 @ X37) @ 
% 2.74/2.94               (k2_zfmisc_1 @ X39 @ X37)))),
% 2.74/2.94      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.74/2.94  thf('99', plain,
% 2.74/2.94      (((r1_tarski @ sk_A @ sk_C_1) | ((sk_B_1) = (k1_xboole_0)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['97', '98'])).
% 2.74/2.94  thf('100', plain,
% 2.74/2.94      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 2.74/2.94      inference('split', [status(esa)], ['26'])).
% 2.74/2.94  thf('101', plain,
% 2.74/2.94      ((((sk_B_1) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['99', '100'])).
% 2.74/2.94  thf('102', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 2.74/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.74/2.94  thf('103', plain,
% 2.74/2.94      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 2.74/2.94         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['101', '102'])).
% 2.74/2.94  thf('104', plain,
% 2.74/2.94      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 2.74/2.94      inference('sup-', [status(thm)], ['78', '103'])).
% 2.74/2.94  thf('105', plain, (((r1_tarski @ sk_A @ sk_C_1))),
% 2.74/2.94      inference('simplify', [status(thm)], ['104'])).
% 2.74/2.94  thf('106', plain,
% 2.74/2.94      (~ ((r1_tarski @ sk_B_1 @ sk_D_1)) | ~ ((r1_tarski @ sk_A @ sk_C_1))),
% 2.74/2.94      inference('split', [status(esa)], ['26'])).
% 2.74/2.94  thf('107', plain, (~ ((r1_tarski @ sk_B_1 @ sk_D_1))),
% 2.74/2.94      inference('sat_resolution*', [status(thm)], ['105', '106'])).
% 2.74/2.94  thf('108', plain, (((sk_A) = (k1_xboole_0))),
% 2.74/2.94      inference('simpl_trail', [status(thm)], ['64', '107'])).
% 2.74/2.94  thf('109', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]:
% 2.74/2.94         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 2.74/2.94          | (zip_tseitin_0 @ 
% 2.74/2.94             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.74/2.94             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 2.74/2.94             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 2.74/2.94      inference('sup-', [status(thm)], ['65', '67'])).
% 2.74/2.94  thf('110', plain,
% 2.74/2.94      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.74/2.94         ((r2_hidden @ X21 @ X25)
% 2.74/2.94          | ~ (zip_tseitin_0 @ X22 @ X21 @ X23 @ X24 @ X25))),
% 2.74/2.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.74/2.94  thf('111', plain,
% 2.74/2.94      (![X0 : $i, X1 : $i]:
% 2.74/2.94         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0))
% 2.74/2.94          | (r2_hidden @ 
% 2.74/2.94             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['109', '110'])).
% 2.74/2.94  thf('112', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 2.74/2.94      inference('demod', [status(thm)], ['73', '76'])).
% 2.74/2.94  thf('113', plain,
% 2.74/2.94      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.74/2.94      inference('sup-', [status(thm)], ['111', '112'])).
% 2.74/2.94  thf('114', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 2.74/2.94      inference('demod', [status(thm)], ['0', '108', '113'])).
% 2.74/2.94  thf('115', plain, ($false), inference('simplify', [status(thm)], ['114'])).
% 2.74/2.94  
% 2.74/2.94  % SZS output end Refutation
% 2.74/2.94  
% 2.74/2.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
