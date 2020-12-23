%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cueSgItnxM

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:42 EST 2020

% Result     : Theorem 14.85s
% Output     : Refutation 14.85s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 243 expanded)
%              Number of leaves         :   20 (  84 expanded)
%              Depth                    :   20
%              Number of atoms          :  689 (2186 expanded)
%              Number of equality atoms :   67 ( 209 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
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

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X23 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('7',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X23 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X21 @ X20 ) @ ( k2_zfmisc_1 @ X22 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
      | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['20','27','28'])).

thf('30',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('37',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ X30 @ ( k4_xboole_0 @ X27 @ X29 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X27 ) @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['31','40'])).

thf('42',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','43'])).

thf('45',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X23 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('52',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('57',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['53'])).

thf('59',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['53'])).

thf('61',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['54','61'])).

thf('63',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['52','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X27 @ X29 ) @ X28 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','63','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cueSgItnxM
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:36 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 14.85/15.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 14.85/15.04  % Solved by: fo/fo7.sh
% 14.85/15.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.85/15.04  % done 6860 iterations in 14.582s
% 14.85/15.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 14.85/15.04  % SZS output start Refutation
% 14.85/15.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.85/15.04  thf(sk_D_type, type, sk_D: $i).
% 14.85/15.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.85/15.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 14.85/15.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 14.85/15.04  thf(sk_B_1_type, type, sk_B_1: $i).
% 14.85/15.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 14.85/15.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 14.85/15.04  thf(sk_A_type, type, sk_A: $i).
% 14.85/15.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 14.85/15.04  thf(t138_zfmisc_1, conjecture,
% 14.85/15.04    (![A:$i,B:$i,C:$i,D:$i]:
% 14.85/15.04     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 14.85/15.04       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 14.85/15.04         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 14.85/15.04  thf(zf_stmt_0, negated_conjecture,
% 14.85/15.04    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 14.85/15.04        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 14.85/15.04          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 14.85/15.04            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 14.85/15.04    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 14.85/15.04  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 14.85/15.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.85/15.04  thf('1', plain,
% 14.85/15.04      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 14.85/15.04        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 14.85/15.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.85/15.04  thf(t28_xboole_1, axiom,
% 14.85/15.04    (![A:$i,B:$i]:
% 14.85/15.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 14.85/15.04  thf('2', plain,
% 14.85/15.04      (![X17 : $i, X18 : $i]:
% 14.85/15.04         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 14.85/15.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 14.85/15.04  thf('3', plain,
% 14.85/15.04      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 14.85/15.04         (k2_zfmisc_1 @ sk_C_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 14.85/15.04      inference('sup-', [status(thm)], ['1', '2'])).
% 14.85/15.04  thf(commutativity_k3_xboole_0, axiom,
% 14.85/15.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 14.85/15.04  thf('4', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.85/15.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.85/15.04  thf('5', plain,
% 14.85/15.04      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 14.85/15.04         (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 14.85/15.04      inference('demod', [status(thm)], ['3', '4'])).
% 14.85/15.04  thf(t123_zfmisc_1, axiom,
% 14.85/15.04    (![A:$i,B:$i,C:$i,D:$i]:
% 14.85/15.04     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 14.85/15.04       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 14.85/15.04  thf('6', plain,
% 14.85/15.04      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 14.85/15.04         ((k2_zfmisc_1 @ (k3_xboole_0 @ X23 @ X25) @ (k3_xboole_0 @ X24 @ X26))
% 14.85/15.04           = (k3_xboole_0 @ (k2_zfmisc_1 @ X23 @ X24) @ 
% 14.85/15.04              (k2_zfmisc_1 @ X25 @ X26)))),
% 14.85/15.04      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 14.85/15.04  thf('7', plain,
% 14.85/15.04      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 14.85/15.04         (k3_xboole_0 @ sk_D @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 14.85/15.04      inference('demod', [status(thm)], ['5', '6'])).
% 14.85/15.04  thf(idempotence_k3_xboole_0, axiom,
% 14.85/15.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 14.85/15.04  thf('8', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 14.85/15.04      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 14.85/15.04  thf('9', plain,
% 14.85/15.04      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 14.85/15.04         ((k2_zfmisc_1 @ (k3_xboole_0 @ X23 @ X25) @ (k3_xboole_0 @ X24 @ X26))
% 14.85/15.04           = (k3_xboole_0 @ (k2_zfmisc_1 @ X23 @ X24) @ 
% 14.85/15.04              (k2_zfmisc_1 @ X25 @ X26)))),
% 14.85/15.04      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 14.85/15.04  thf('10', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.85/15.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.85/15.04  thf(t17_xboole_1, axiom,
% 14.85/15.04    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 14.85/15.04  thf('11', plain,
% 14.85/15.04      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 14.85/15.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 14.85/15.04  thf('12', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 14.85/15.04      inference('sup+', [status(thm)], ['10', '11'])).
% 14.85/15.04  thf('13', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.85/15.04         (r1_tarski @ 
% 14.85/15.04          (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 14.85/15.04          (k2_zfmisc_1 @ X2 @ X0))),
% 14.85/15.04      inference('sup+', [status(thm)], ['9', '12'])).
% 14.85/15.04  thf('14', plain,
% 14.85/15.04      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 14.85/15.04         (k3_xboole_0 @ sk_D @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 14.85/15.04      inference('demod', [status(thm)], ['5', '6'])).
% 14.85/15.04  thf(t117_zfmisc_1, axiom,
% 14.85/15.04    (![A:$i,B:$i,C:$i]:
% 14.85/15.04     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 14.85/15.04          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 14.85/15.04            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 14.85/15.04          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 14.85/15.04  thf('15', plain,
% 14.85/15.04      (![X20 : $i, X21 : $i, X22 : $i]:
% 14.85/15.04         (((X20) = (k1_xboole_0))
% 14.85/15.04          | (r1_tarski @ X21 @ X22)
% 14.85/15.04          | ~ (r1_tarski @ (k2_zfmisc_1 @ X21 @ X20) @ 
% 14.85/15.04               (k2_zfmisc_1 @ X22 @ X20)))),
% 14.85/15.04      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 14.85/15.04  thf('16', plain,
% 14.85/15.04      (![X0 : $i]:
% 14.85/15.04         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B_1)) @ 
% 14.85/15.04             (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 14.85/15.04          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_C_1 @ sk_A))
% 14.85/15.04          | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 14.85/15.04      inference('sup-', [status(thm)], ['14', '15'])).
% 14.85/15.04  thf('17', plain,
% 14.85/15.04      (![X0 : $i]:
% 14.85/15.04         (((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))
% 14.85/15.04          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ 
% 14.85/15.04             (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 14.85/15.04      inference('sup-', [status(thm)], ['13', '16'])).
% 14.85/15.04  thf('18', plain,
% 14.85/15.04      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A))
% 14.85/15.04        | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 14.85/15.04      inference('sup+', [status(thm)], ['8', '17'])).
% 14.85/15.04  thf('19', plain,
% 14.85/15.04      (![X17 : $i, X18 : $i]:
% 14.85/15.04         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 14.85/15.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 14.85/15.04  thf('20', plain,
% 14.85/15.04      ((((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))
% 14.85/15.04        | ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)) = (sk_A)))),
% 14.85/15.04      inference('sup-', [status(thm)], ['18', '19'])).
% 14.85/15.04  thf('21', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.85/15.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.85/15.04  thf('22', plain,
% 14.85/15.04      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 14.85/15.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 14.85/15.04  thf('23', plain,
% 14.85/15.04      (![X17 : $i, X18 : $i]:
% 14.85/15.04         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 14.85/15.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 14.85/15.04  thf('24', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]:
% 14.85/15.04         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 14.85/15.04           = (k3_xboole_0 @ X0 @ X1))),
% 14.85/15.04      inference('sup-', [status(thm)], ['22', '23'])).
% 14.85/15.04  thf('25', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.85/15.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.85/15.04  thf('26', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]:
% 14.85/15.04         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 14.85/15.04           = (k3_xboole_0 @ X0 @ X1))),
% 14.85/15.04      inference('demod', [status(thm)], ['24', '25'])).
% 14.85/15.04  thf('27', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]:
% 14.85/15.04         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 14.85/15.04           = (k3_xboole_0 @ X0 @ X1))),
% 14.85/15.04      inference('sup+', [status(thm)], ['21', '26'])).
% 14.85/15.04  thf('28', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.85/15.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.85/15.04  thf('29', plain,
% 14.85/15.04      ((((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))
% 14.85/15.04        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A)))),
% 14.85/15.04      inference('demod', [status(thm)], ['20', '27', '28'])).
% 14.85/15.04  thf('30', plain,
% 14.85/15.04      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 14.85/15.04         (k3_xboole_0 @ sk_D @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 14.85/15.04      inference('demod', [status(thm)], ['5', '6'])).
% 14.85/15.04  thf('31', plain,
% 14.85/15.04      ((((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ k1_xboole_0)
% 14.85/15.04          = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 14.85/15.04        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A)))),
% 14.85/15.04      inference('sup+', [status(thm)], ['29', '30'])).
% 14.85/15.04  thf('32', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 14.85/15.04      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 14.85/15.04  thf(t100_xboole_1, axiom,
% 14.85/15.04    (![A:$i,B:$i]:
% 14.85/15.04     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 14.85/15.04  thf('33', plain,
% 14.85/15.04      (![X10 : $i, X11 : $i]:
% 14.85/15.04         ((k4_xboole_0 @ X10 @ X11)
% 14.85/15.04           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 14.85/15.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 14.85/15.04  thf('34', plain,
% 14.85/15.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 14.85/15.04      inference('sup+', [status(thm)], ['32', '33'])).
% 14.85/15.04  thf(t92_xboole_1, axiom,
% 14.85/15.04    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 14.85/15.04  thf('35', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 14.85/15.04      inference('cnf', [status(esa)], [t92_xboole_1])).
% 14.85/15.04  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.85/15.04      inference('demod', [status(thm)], ['34', '35'])).
% 14.85/15.04  thf(t125_zfmisc_1, axiom,
% 14.85/15.04    (![A:$i,B:$i,C:$i]:
% 14.85/15.04     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 14.85/15.04         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 14.85/15.04       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 14.85/15.04         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 14.85/15.04  thf('37', plain,
% 14.85/15.04      (![X27 : $i, X29 : $i, X30 : $i]:
% 14.85/15.04         ((k2_zfmisc_1 @ X30 @ (k4_xboole_0 @ X27 @ X29))
% 14.85/15.04           = (k4_xboole_0 @ (k2_zfmisc_1 @ X30 @ X27) @ 
% 14.85/15.04              (k2_zfmisc_1 @ X30 @ X29)))),
% 14.85/15.04      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 14.85/15.04  thf('38', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]:
% 14.85/15.04         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 14.85/15.04      inference('sup+', [status(thm)], ['36', '37'])).
% 14.85/15.04  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.85/15.04      inference('demod', [status(thm)], ['34', '35'])).
% 14.85/15.04  thf('40', plain,
% 14.85/15.04      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.85/15.04      inference('demod', [status(thm)], ['38', '39'])).
% 14.85/15.04  thf('41', plain,
% 14.85/15.04      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 14.85/15.04        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A)))),
% 14.85/15.04      inference('demod', [status(thm)], ['31', '40'])).
% 14.85/15.04  thf('42', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 14.85/15.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.85/15.04  thf('43', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 14.85/15.04      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 14.85/15.04  thf('44', plain,
% 14.85/15.04      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B_1))
% 14.85/15.04         = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 14.85/15.04      inference('demod', [status(thm)], ['7', '43'])).
% 14.85/15.04  thf('45', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 14.85/15.04      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 14.85/15.04  thf('46', plain,
% 14.85/15.04      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 14.85/15.04         ((k2_zfmisc_1 @ (k3_xboole_0 @ X23 @ X25) @ (k3_xboole_0 @ X24 @ X26))
% 14.85/15.04           = (k3_xboole_0 @ (k2_zfmisc_1 @ X23 @ X24) @ 
% 14.85/15.04              (k2_zfmisc_1 @ X25 @ X26)))),
% 14.85/15.04      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 14.85/15.04  thf('47', plain,
% 14.85/15.04      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 14.85/15.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 14.85/15.04  thf('48', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.85/15.04         (r1_tarski @ 
% 14.85/15.04          (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 14.85/15.04          (k2_zfmisc_1 @ X3 @ X1))),
% 14.85/15.04      inference('sup+', [status(thm)], ['46', '47'])).
% 14.85/15.04  thf('49', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.85/15.04         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 14.85/15.04          (k2_zfmisc_1 @ X0 @ X1))),
% 14.85/15.04      inference('sup+', [status(thm)], ['45', '48'])).
% 14.85/15.04  thf('50', plain,
% 14.85/15.04      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ (k2_zfmisc_1 @ sk_A @ sk_D))),
% 14.85/15.04      inference('sup+', [status(thm)], ['44', '49'])).
% 14.85/15.04  thf('51', plain,
% 14.85/15.04      (![X20 : $i, X21 : $i, X22 : $i]:
% 14.85/15.04         (((X20) = (k1_xboole_0))
% 14.85/15.04          | (r1_tarski @ X21 @ X22)
% 14.85/15.04          | ~ (r1_tarski @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 14.85/15.04               (k2_zfmisc_1 @ X20 @ X22)))),
% 14.85/15.04      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 14.85/15.04  thf('52', plain, (((r1_tarski @ sk_B_1 @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 14.85/15.04      inference('sup-', [status(thm)], ['50', '51'])).
% 14.85/15.04  thf('53', plain,
% 14.85/15.04      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B_1 @ sk_D))),
% 14.85/15.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.85/15.04  thf('54', plain,
% 14.85/15.04      ((~ (r1_tarski @ sk_B_1 @ sk_D)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 14.85/15.04      inference('split', [status(esa)], ['53'])).
% 14.85/15.04  thf('55', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 14.85/15.04      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 14.85/15.04  thf('56', plain,
% 14.85/15.04      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 14.85/15.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 14.85/15.04  thf('57', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 14.85/15.04      inference('sup+', [status(thm)], ['55', '56'])).
% 14.85/15.04  thf('58', plain,
% 14.85/15.04      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 14.85/15.04      inference('split', [status(esa)], ['53'])).
% 14.85/15.04  thf('59', plain, (((r1_tarski @ sk_A @ sk_C_1))),
% 14.85/15.04      inference('sup-', [status(thm)], ['57', '58'])).
% 14.85/15.04  thf('60', plain,
% 14.85/15.04      (~ ((r1_tarski @ sk_B_1 @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C_1))),
% 14.85/15.04      inference('split', [status(esa)], ['53'])).
% 14.85/15.04  thf('61', plain, (~ ((r1_tarski @ sk_B_1 @ sk_D))),
% 14.85/15.04      inference('sat_resolution*', [status(thm)], ['59', '60'])).
% 14.85/15.04  thf('62', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 14.85/15.04      inference('simpl_trail', [status(thm)], ['54', '61'])).
% 14.85/15.04  thf('63', plain, (((sk_A) = (k1_xboole_0))),
% 14.85/15.04      inference('clc', [status(thm)], ['52', '62'])).
% 14.85/15.04  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.85/15.04      inference('demod', [status(thm)], ['34', '35'])).
% 14.85/15.04  thf('65', plain,
% 14.85/15.04      (![X27 : $i, X28 : $i, X29 : $i]:
% 14.85/15.04         ((k2_zfmisc_1 @ (k4_xboole_0 @ X27 @ X29) @ X28)
% 14.85/15.04           = (k4_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28) @ 
% 14.85/15.04              (k2_zfmisc_1 @ X29 @ X28)))),
% 14.85/15.04      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 14.85/15.04  thf('66', plain,
% 14.85/15.04      (![X0 : $i, X1 : $i]:
% 14.85/15.04         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 14.85/15.04      inference('sup+', [status(thm)], ['64', '65'])).
% 14.85/15.04  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.85/15.04      inference('demod', [status(thm)], ['34', '35'])).
% 14.85/15.04  thf('68', plain,
% 14.85/15.04      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 14.85/15.04      inference('demod', [status(thm)], ['66', '67'])).
% 14.85/15.04  thf('69', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 14.85/15.04      inference('demod', [status(thm)], ['0', '63', '68'])).
% 14.85/15.04  thf('70', plain, ($false), inference('simplify', [status(thm)], ['69'])).
% 14.85/15.04  
% 14.85/15.04  % SZS output end Refutation
% 14.85/15.04  
% 14.85/15.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
