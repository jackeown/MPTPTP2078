%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BnqHRGNeZ2

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:24 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 769 expanded)
%              Number of leaves         :   29 ( 247 expanded)
%              Depth                    :   24
%              Number of atoms          : 1102 (7694 expanded)
%              Number of equality atoms :  194 (1430 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

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
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,
    ( ( k1_tarski @ sk_A_1 )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_C_1
     != ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A_1 ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A_1 ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_A_1 )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X56: $i,X57: $i] :
      ( ( X57
        = ( k1_tarski @ X56 ) )
      | ( X57 = k1_xboole_0 )
      | ~ ( r1_tarski @ X57 @ ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A_1 )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1
      = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,
    ( ( k1_tarski @ sk_A_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( sk_B_1
     != ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A_1 ) ),
    inference('sat_resolution*',[status(thm)],['6','8','28'])).

thf('30',plain,(
    sk_C_1
 != ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['5','29'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('35',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,
    ( ( sk_B_1
      = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','39'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('50',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('59',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['56','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['49','72'])).

thf('74',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
      = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','73'])).

thf('75',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['56','71'])).

thf('77',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['56','71'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
      = ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('85',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k5_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['56','71'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_B_1
      = ( k5_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','39'])).

thf('93',plain,
    ( ( sk_B_1
      = ( k3_tarski @ ( k2_tarski @ sk_C_1 @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('95',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B_1
      = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1
      = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( sk_C_1
      = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('103',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('104',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_B_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_C_1
 != ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['5','29'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1
         != ( k3_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('110',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('111',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('112',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('113',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('114',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['111','114'])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['110','115'])).

thf('117',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['108','109','116'])).

thf('118',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('120',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['118','119'])).

thf('121',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['101','120'])).

thf('122',plain,(
    sk_C_1
 != ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['5','29'])).

thf('123',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['100','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['47','123'])).

thf('125',plain,(
    sk_C_1 != sk_C_1 ),
    inference(demod,[status(thm)],['30','124'])).

thf('126',plain,(
    $false ),
    inference(simplify,[status(thm)],['125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BnqHRGNeZ2
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:23:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.15  % Solved by: fo/fo7.sh
% 0.91/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.15  % done 2156 iterations in 0.694s
% 0.91/1.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.15  % SZS output start Refutation
% 0.91/1.15  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.15  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.91/1.15  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.15  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.91/1.15  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.91/1.15  thf(t43_zfmisc_1, conjecture,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.91/1.15          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.91/1.15          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.91/1.15          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.91/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.15    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.15        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.91/1.15             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.91/1.15             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.91/1.15             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.91/1.15    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.91/1.15  thf('0', plain,
% 0.91/1.15      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A_1)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('1', plain,
% 0.91/1.15      ((((sk_C_1) != (k1_tarski @ sk_A_1)))
% 0.91/1.15         <= (~ (((sk_C_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('split', [status(esa)], ['0'])).
% 0.91/1.15  thf('2', plain, (((k1_tarski @ sk_A_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(l51_zfmisc_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.15  thf('3', plain,
% 0.91/1.15      (![X59 : $i, X60 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.91/1.15      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.15  thf('4', plain,
% 0.91/1.15      (((k1_tarski @ sk_A_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.91/1.15      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.15  thf('5', plain,
% 0.91/1.15      ((((sk_C_1) != (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1))))
% 0.91/1.15         <= (~ (((sk_C_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('demod', [status(thm)], ['1', '4'])).
% 0.91/1.15  thf('6', plain,
% 0.91/1.15      (~ (((sk_C_1) = (k1_tarski @ sk_A_1))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('split', [status(esa)], ['0'])).
% 0.91/1.15  thf('7', plain,
% 0.91/1.15      ((((sk_B_1) != (k1_tarski @ sk_A_1)) | ((sk_C_1) != (k1_tarski @ sk_A_1)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('8', plain,
% 0.91/1.15      (~ (((sk_C_1) = (k1_tarski @ sk_A_1))) | 
% 0.91/1.15       ~ (((sk_B_1) = (k1_tarski @ sk_A_1)))),
% 0.91/1.15      inference('split', [status(esa)], ['7'])).
% 0.91/1.15  thf(t7_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.15  thf('9', plain,
% 0.91/1.15      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.91/1.15      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.91/1.15  thf('10', plain,
% 0.91/1.15      (![X59 : $i, X60 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.91/1.15      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.15  thf('11', plain,
% 0.91/1.15      (![X21 : $i, X22 : $i]:
% 0.91/1.15         (r1_tarski @ X21 @ (k3_tarski @ (k2_tarski @ X21 @ X22)))),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('12', plain,
% 0.91/1.15      (((k1_tarski @ sk_A_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.91/1.15      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.15  thf(l3_zfmisc_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.91/1.15       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.91/1.15  thf('13', plain,
% 0.91/1.15      (![X56 : $i, X57 : $i]:
% 0.91/1.15         (((X57) = (k1_tarski @ X56))
% 0.91/1.15          | ((X57) = (k1_xboole_0))
% 0.91/1.15          | ~ (r1_tarski @ X57 @ (k1_tarski @ X56)))),
% 0.91/1.15      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.91/1.15  thf('14', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.91/1.15          | ((X0) = (k1_xboole_0))
% 0.91/1.15          | ((X0) = (k1_tarski @ sk_A_1)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['12', '13'])).
% 0.91/1.15  thf('15', plain,
% 0.91/1.15      (((k1_tarski @ sk_A_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.91/1.15      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.15  thf('16', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.91/1.15          | ((X0) = (k1_xboole_0))
% 0.91/1.15          | ((X0) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1))))),
% 0.91/1.15      inference('demod', [status(thm)], ['14', '15'])).
% 0.91/1.15  thf('17', plain,
% 0.91/1.15      ((((sk_B_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['11', '16'])).
% 0.91/1.15  thf('18', plain,
% 0.91/1.15      (![X59 : $i, X60 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.91/1.15      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.15  thf('19', plain, (((k1_tarski @ sk_A_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('20', plain,
% 0.91/1.15      ((((sk_B_1) != (k1_tarski @ sk_A_1)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('21', plain,
% 0.91/1.15      ((((sk_B_1) != (k1_tarski @ sk_A_1)))
% 0.91/1.15         <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('split', [status(esa)], ['20'])).
% 0.91/1.15  thf('22', plain,
% 0.91/1.15      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.91/1.15         <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['19', '21'])).
% 0.91/1.15  thf('23', plain,
% 0.91/1.15      ((((sk_B_1) != (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1))))
% 0.91/1.15         <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['18', '22'])).
% 0.91/1.15  thf('24', plain,
% 0.91/1.15      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.91/1.15         <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['17', '23'])).
% 0.91/1.15  thf('25', plain,
% 0.91/1.15      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('simplify', [status(thm)], ['24'])).
% 0.91/1.15  thf('26', plain,
% 0.91/1.15      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.15      inference('split', [status(esa)], ['0'])).
% 0.91/1.15  thf('27', plain,
% 0.91/1.15      ((((sk_B_1) != (sk_B_1)))
% 0.91/1.15         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.91/1.15             ~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['25', '26'])).
% 0.91/1.15  thf('28', plain,
% 0.91/1.15      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A_1)))),
% 0.91/1.15      inference('simplify', [status(thm)], ['27'])).
% 0.91/1.15  thf('29', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A_1)))),
% 0.91/1.15      inference('sat_resolution*', [status(thm)], ['6', '8', '28'])).
% 0.91/1.15  thf('30', plain, (((sk_C_1) != (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.91/1.15      inference('simpl_trail', [status(thm)], ['5', '29'])).
% 0.91/1.15  thf(commutativity_k5_xboole_0, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.91/1.15  thf('31', plain,
% 0.91/1.15      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.15  thf(t5_boole, axiom,
% 0.91/1.15    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.15  thf('32', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.91/1.15      inference('cnf', [status(esa)], [t5_boole])).
% 0.91/1.15  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['31', '32'])).
% 0.91/1.15  thf(t94_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k2_xboole_0 @ A @ B ) =
% 0.91/1.15       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.15  thf('34', plain,
% 0.91/1.15      (![X26 : $i, X27 : $i]:
% 0.91/1.15         ((k2_xboole_0 @ X26 @ X27)
% 0.91/1.15           = (k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ 
% 0.91/1.15              (k3_xboole_0 @ X26 @ X27)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.91/1.15  thf('35', plain,
% 0.91/1.15      (![X59 : $i, X60 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.91/1.15      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.15  thf(t91_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.15       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.91/1.15  thf('36', plain,
% 0.91/1.15      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.15         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.91/1.15           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.15  thf(commutativity_k3_xboole_0, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.91/1.15  thf('37', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.15  thf(t100_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.15  thf('38', plain,
% 0.91/1.15      (![X13 : $i, X14 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X13 @ X14)
% 0.91/1.15           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.15  thf('39', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X0 @ X1)
% 0.91/1.15           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['37', '38'])).
% 0.91/1.15  thf('40', plain,
% 0.91/1.15      (![X26 : $i, X27 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X26 @ X27))
% 0.91/1.15           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.91/1.15      inference('demod', [status(thm)], ['34', '35', '36', '39'])).
% 0.91/1.15  thf('41', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0))
% 0.91/1.15           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['33', '40'])).
% 0.91/1.15  thf(t2_boole, axiom,
% 0.91/1.15    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.91/1.15  thf('42', plain,
% 0.91/1.15      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.15      inference('cnf', [status(esa)], [t2_boole])).
% 0.91/1.15  thf('43', plain,
% 0.91/1.15      (![X13 : $i, X14 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X13 @ X14)
% 0.91/1.15           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.15  thf('44', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['42', '43'])).
% 0.91/1.15  thf('45', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.91/1.15      inference('cnf', [status(esa)], [t5_boole])).
% 0.91/1.15  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['44', '45'])).
% 0.91/1.15  thf('47', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 0.91/1.15      inference('demod', [status(thm)], ['41', '46'])).
% 0.91/1.15  thf('48', plain,
% 0.91/1.15      ((((sk_B_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['11', '16'])).
% 0.91/1.15  thf('49', plain,
% 0.91/1.15      (![X26 : $i, X27 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X26 @ X27))
% 0.91/1.15           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.91/1.15      inference('demod', [status(thm)], ['34', '35', '36', '39'])).
% 0.91/1.15  thf(idempotence_k3_xboole_0, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.91/1.15  thf('50', plain, (![X11 : $i]: ((k3_xboole_0 @ X11 @ X11) = (X11))),
% 0.91/1.15      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.91/1.15  thf('51', plain,
% 0.91/1.15      (![X13 : $i, X14 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X13 @ X14)
% 0.91/1.15           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.15  thf('52', plain,
% 0.91/1.15      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['50', '51'])).
% 0.91/1.15  thf('53', plain,
% 0.91/1.15      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.15  thf('54', plain,
% 0.91/1.15      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.15         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.91/1.15           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.15  thf('55', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.91/1.15           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.15  thf('56', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.91/1.15           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['52', '55'])).
% 0.91/1.15  thf('57', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 0.91/1.15      inference('demod', [status(thm)], ['41', '46'])).
% 0.91/1.15  thf(t40_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.91/1.15  thf('58', plain,
% 0.91/1.15      (![X16 : $i, X17 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.91/1.15           = (k4_xboole_0 @ X16 @ X17))),
% 0.91/1.15      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.91/1.15  thf('59', plain,
% 0.91/1.15      (![X59 : $i, X60 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.91/1.15      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.15  thf('60', plain,
% 0.91/1.15      (![X16 : $i, X17 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X16 @ X17)) @ X17)
% 0.91/1.15           = (k4_xboole_0 @ X16 @ X17))),
% 0.91/1.15      inference('demod', [status(thm)], ['58', '59'])).
% 0.91/1.15  thf('61', plain,
% 0.91/1.15      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['57', '60'])).
% 0.91/1.15  thf('62', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.15  thf('63', plain,
% 0.91/1.15      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.15      inference('cnf', [status(esa)], [t2_boole])).
% 0.91/1.15  thf('64', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['62', '63'])).
% 0.91/1.15  thf('65', plain,
% 0.91/1.15      (![X13 : $i, X14 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X13 @ X14)
% 0.91/1.15           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.15  thf('66', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.91/1.15           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['64', '65'])).
% 0.91/1.15  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['31', '32'])).
% 0.91/1.15  thf('68', plain,
% 0.91/1.15      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['66', '67'])).
% 0.91/1.15  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['61', '68'])).
% 0.91/1.15  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['31', '32'])).
% 0.91/1.15  thf('71', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.91/1.15      inference('sup+', [status(thm)], ['69', '70'])).
% 0.91/1.15  thf('72', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.91/1.15      inference('demod', [status(thm)], ['56', '71'])).
% 0.91/1.15  thf('73', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X0 @ X1)
% 0.91/1.15           = (k5_xboole_0 @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.91/1.15      inference('sup+', [status(thm)], ['49', '72'])).
% 0.91/1.15  thf('74', plain,
% 0.91/1.15      ((((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['48', '73'])).
% 0.91/1.15  thf('75', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.91/1.15      inference('cnf', [status(esa)], [t5_boole])).
% 0.91/1.15  thf('76', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.91/1.15      inference('demod', [status(thm)], ['56', '71'])).
% 0.91/1.15  thf('77', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['75', '76'])).
% 0.91/1.15  thf('78', plain,
% 0.91/1.15      ((((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('demod', [status(thm)], ['74', '77'])).
% 0.91/1.15  thf('79', plain,
% 0.91/1.15      (![X13 : $i, X14 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X13 @ X14)
% 0.91/1.15           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.15  thf('80', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.91/1.15      inference('demod', [status(thm)], ['56', '71'])).
% 0.91/1.15  thf('81', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X1 @ X0)
% 0.91/1.15           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['79', '80'])).
% 0.91/1.15  thf('82', plain,
% 0.91/1.15      ((((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k5_xboole_0 @ sk_C_1 @ k1_xboole_0))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['78', '81'])).
% 0.91/1.15  thf('83', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.15  thf('84', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.91/1.15      inference('cnf', [status(esa)], [t5_boole])).
% 0.91/1.15  thf('85', plain,
% 0.91/1.15      ((((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.91/1.15  thf('86', plain,
% 0.91/1.15      (![X13 : $i, X14 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X13 @ X14)
% 0.91/1.15           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.15  thf('87', plain,
% 0.91/1.15      ((((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (k5_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['85', '86'])).
% 0.91/1.15  thf('88', plain,
% 0.91/1.15      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.15  thf('89', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.91/1.15      inference('demod', [status(thm)], ['56', '71'])).
% 0.91/1.15  thf('90', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['88', '89'])).
% 0.91/1.15  thf('91', plain,
% 0.91/1.15      ((((sk_B_1) = (k5_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['87', '90'])).
% 0.91/1.15  thf('92', plain,
% 0.91/1.15      (![X26 : $i, X27 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X26 @ X27))
% 0.91/1.15           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 0.91/1.15      inference('demod', [status(thm)], ['34', '35', '36', '39'])).
% 0.91/1.15  thf('93', plain,
% 0.91/1.15      ((((sk_B_1) = (k3_tarski @ (k2_tarski @ sk_C_1 @ sk_B_1)))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('demod', [status(thm)], ['91', '92'])).
% 0.91/1.15  thf('94', plain,
% 0.91/1.15      (![X21 : $i, X22 : $i]:
% 0.91/1.15         (r1_tarski @ X21 @ (k3_tarski @ (k2_tarski @ X21 @ X22)))),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('95', plain,
% 0.91/1.15      (((r1_tarski @ sk_C_1 @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['93', '94'])).
% 0.91/1.15  thf('96', plain,
% 0.91/1.15      ((((sk_B_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['11', '16'])).
% 0.91/1.15  thf('97', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.91/1.15          | ((X0) = (k1_xboole_0))
% 0.91/1.15          | ((X0) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1))))),
% 0.91/1.15      inference('demod', [status(thm)], ['14', '15'])).
% 0.91/1.15  thf('98', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (r1_tarski @ X0 @ sk_B_1)
% 0.91/1.15          | ((sk_B_1) = (k1_xboole_0))
% 0.91/1.15          | ((X0) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.91/1.15          | ((X0) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['96', '97'])).
% 0.91/1.15  thf('99', plain,
% 0.91/1.15      ((((sk_B_1) = (k1_xboole_0))
% 0.91/1.15        | ((sk_C_1) = (k1_xboole_0))
% 0.91/1.15        | ((sk_C_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['95', '98'])).
% 0.91/1.15  thf('100', plain,
% 0.91/1.15      ((((sk_C_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))
% 0.91/1.15        | ((sk_C_1) = (k1_xboole_0))
% 0.91/1.15        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('simplify', [status(thm)], ['99'])).
% 0.91/1.15  thf('101', plain,
% 0.91/1.15      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.91/1.15      inference('split', [status(esa)], ['20'])).
% 0.91/1.15  thf('102', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 0.91/1.15      inference('demod', [status(thm)], ['41', '46'])).
% 0.91/1.15  thf('103', plain,
% 0.91/1.15      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('simplify', [status(thm)], ['24'])).
% 0.91/1.15  thf(l13_xboole_0, axiom,
% 0.91/1.15    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.15  thf('104', plain,
% 0.91/1.15      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X12))),
% 0.91/1.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.15  thf('105', plain,
% 0.91/1.15      ((![X0 : $i]: (((X0) = (sk_B_1)) | ~ (v1_xboole_0 @ X0)))
% 0.91/1.15         <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('sup+', [status(thm)], ['103', '104'])).
% 0.91/1.15  thf('106', plain,
% 0.91/1.15      (((sk_C_1) != (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.91/1.15      inference('simpl_trail', [status(thm)], ['5', '29'])).
% 0.91/1.15  thf('107', plain,
% 0.91/1.15      ((![X0 : $i]:
% 0.91/1.15          (((sk_C_1) != (k3_tarski @ (k2_tarski @ X0 @ sk_C_1)))
% 0.91/1.15           | ~ (v1_xboole_0 @ X0)))
% 0.91/1.15         <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['105', '106'])).
% 0.91/1.15  thf('108', plain,
% 0.91/1.15      (((((sk_C_1) != (sk_C_1)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.91/1.15         <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['102', '107'])).
% 0.91/1.15  thf('109', plain,
% 0.91/1.15      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('simplify', [status(thm)], ['24'])).
% 0.91/1.15  thf('110', plain,
% 0.91/1.15      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('simplify', [status(thm)], ['24'])).
% 0.91/1.15  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.91/1.15  thf('111', plain, ((v1_xboole_0 @ sk_A)),
% 0.91/1.15      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.91/1.15  thf('112', plain, ((v1_xboole_0 @ sk_A)),
% 0.91/1.15      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.91/1.15  thf('113', plain,
% 0.91/1.15      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X12))),
% 0.91/1.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.15  thf('114', plain, (((sk_A) = (k1_xboole_0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['112', '113'])).
% 0.91/1.15  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.15      inference('demod', [status(thm)], ['111', '114'])).
% 0.91/1.15  thf('116', plain,
% 0.91/1.15      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('sup+', [status(thm)], ['110', '115'])).
% 0.91/1.15  thf('117', plain,
% 0.91/1.15      ((((sk_C_1) != (sk_C_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A_1))))),
% 0.91/1.15      inference('demod', [status(thm)], ['108', '109', '116'])).
% 0.91/1.15  thf('118', plain, ((((sk_B_1) = (k1_tarski @ sk_A_1)))),
% 0.91/1.15      inference('simplify', [status(thm)], ['117'])).
% 0.91/1.15  thf('119', plain,
% 0.91/1.15      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A_1)))),
% 0.91/1.15      inference('split', [status(esa)], ['20'])).
% 0.91/1.15  thf('120', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.91/1.15      inference('sat_resolution*', [status(thm)], ['118', '119'])).
% 0.91/1.15  thf('121', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.91/1.15      inference('simpl_trail', [status(thm)], ['101', '120'])).
% 0.91/1.15  thf('122', plain,
% 0.91/1.15      (((sk_C_1) != (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.91/1.15      inference('simpl_trail', [status(thm)], ['5', '29'])).
% 0.91/1.15  thf('123', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.91/1.15      inference('simplify_reflect-', [status(thm)], ['100', '121', '122'])).
% 0.91/1.15  thf('124', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ sk_B_1 @ X0)) = (X0))),
% 0.91/1.15      inference('demod', [status(thm)], ['47', '123'])).
% 0.91/1.15  thf('125', plain, (((sk_C_1) != (sk_C_1))),
% 0.91/1.15      inference('demod', [status(thm)], ['30', '124'])).
% 0.91/1.15  thf('126', plain, ($false), inference('simplify', [status(thm)], ['125'])).
% 0.91/1.15  
% 0.91/1.15  % SZS output end Refutation
% 0.91/1.15  
% 0.91/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
