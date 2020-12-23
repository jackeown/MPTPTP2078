%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hztmehgxyV

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:36 EST 2020

% Result     : Theorem 29.28s
% Output     : Refutation 29.28s
% Verified   : 
% Statistics : Number of formulae       :  241 (1581 expanded)
%              Number of leaves         :   33 ( 518 expanded)
%              Depth                    :   25
%              Number of atoms          : 2131 (15952 expanded)
%              Number of equality atoms :  253 (2052 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('0',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ( k2_zfmisc_1 @ X61 @ ( k4_xboole_0 @ X58 @ X60 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X61 @ X58 ) @ ( k2_zfmisc_1 @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X58 @ X60 ) @ X59 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X58 @ X59 ) @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('4',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X41 @ X40 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,
    ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_D )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_D )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('10',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X54 @ X56 ) @ ( k3_xboole_0 @ X55 @ X57 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X54 @ X56 ) @ ( k3_xboole_0 @ X55 @ X57 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_C ) @ ( k3_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('15',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X46 @ X48 ) @ X47 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( k2_zfmisc_1 @ X49 @ ( k2_xboole_0 @ X46 @ X48 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X49 @ X46 ) @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('18',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X54 @ X56 ) @ ( k3_xboole_0 @ X55 @ X57 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_D ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X54 @ X56 ) @ ( k3_xboole_0 @ X55 @ X57 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X1 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_D ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_D ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('30',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('31',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( r1_tarski @ X44 @ X45 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X44 @ X43 ) @ ( k2_zfmisc_1 @ X45 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('41',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X36 @ ( k4_xboole_0 @ X37 @ X38 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('47',plain,(
    ! [X39: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X39 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X30 @ X31 ) @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X39: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X39 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','56'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','59'])).

thf('61',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X36 @ ( k4_xboole_0 @ X37 @ X38 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X46 @ X48 ) @ X47 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X54 @ X56 ) @ ( k3_xboole_0 @ X55 @ X57 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X46 @ X48 ) @ X47 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X1 ) ) @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( k2_zfmisc_1 @ X49 @ ( k2_xboole_0 @ X46 @ X48 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X49 @ X46 ) @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('79',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('80',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('82',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','80','84'])).

thf('86',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('89',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('93',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C )
    = sk_C ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( k2_zfmisc_1 @ X49 @ ( k2_xboole_0 @ X46 @ X48 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X49 @ X46 ) @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('96',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( r1_tarski @ X44 @ X45 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X44 @ X43 ) @ ( k2_zfmisc_1 @ X45 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('104',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( k2_zfmisc_1 @ X49 @ ( k2_xboole_0 @ X46 @ X48 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X49 @ X46 ) @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X46 @ X48 ) @ X47 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X46 @ X47 ) @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('108',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( r1_tarski @ X44 @ X45 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X43 @ X44 ) @ ( k2_zfmisc_1 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('114',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( k2_zfmisc_1 @ X49 @ ( k2_xboole_0 @ X46 @ X48 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X49 @ X46 ) @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_B ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_B ) @ X0 ) ) )
      = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X54 @ X56 ) @ ( k3_xboole_0 @ X55 @ X57 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('123',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('124',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('125',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k3_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['117','120','121','122','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['112','130'])).

thf('132',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_D ),
    inference('sup-',[status(thm)],['103','131'])).

thf('133',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('134',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('140',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['102','138','139'])).

thf('141',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('142',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('144',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    sk_C = sk_A ),
    inference('sup+',[status(thm)],['93','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','56'])).

thf('148',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_zfmisc_1 @ X41 @ X42 )
        = k1_xboole_0 )
      | ( X41 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('149',plain,(
    ! [X42: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X42 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','145','146','147','149'])).

thf('151',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['134','137'])).

thf('153',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X30 @ X31 ) @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('154',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( ( k4_xboole_0 @ X25 @ X24 )
       != ( k4_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
     != ( k4_xboole_0 @ sk_D @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','155'])).

thf('157',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['134','137'])).

thf('158',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
     != ( k4_xboole_0 @ sk_D @ sk_B ) )
    | ( sk_B = sk_D ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['134','137'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('160',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('161',plain,
    ( ( k5_xboole_0 @ sk_D @ sk_B )
    = ( k4_xboole_0 @ sk_D @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('162',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k3_xboole_0 @ X34 @ X35 ) )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('163',plain,
    ( ( k5_xboole_0 @ sk_D @ sk_B )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
     != ( k5_xboole_0 @ sk_D @ sk_B ) )
    | ( sk_B = sk_D ) ),
    inference(demod,[status(thm)],['158','163'])).

thf('165',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ( k2_zfmisc_1 @ X61 @ ( k4_xboole_0 @ X58 @ X60 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X61 @ X58 ) @ ( k2_zfmisc_1 @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X58 @ X60 ) @ X59 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X58 @ X59 ) @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('169',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X41 @ X40 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('171',plain,
    ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k5_xboole_0 @ sk_D @ sk_B )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('175',plain,
    ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D )
     != k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['142','143'])).

thf('177',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('178',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('181',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k3_xboole_0 @ X34 @ X35 ) )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['178','179','182'])).

thf('184',plain,
    ( ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_D )
     != k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['175','183'])).

thf('185',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','80','84'])).

thf('186',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('187',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('189',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['178','179','182'])).

thf('191',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X42: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X42 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('193',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['184','191','192'])).

thf('194',plain,
    ( ( k5_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
     != k1_xboole_0 )
    | ( sk_B = sk_D ) ),
    inference(demod,[status(thm)],['164','194'])).

thf('196',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['196'])).

thf('198',plain,(
    sk_C = sk_A ),
    inference('sup+',[status(thm)],['93','144'])).

thf('199',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['196'])).

thf('200',plain,
    ( ( sk_C != sk_C )
   <= ( sk_A != sk_C ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    sk_A = sk_C ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['196'])).

thf('203',plain,(
    sk_B != sk_D ),
    inference('sat_resolution*',[status(thm)],['201','202'])).

thf('204',plain,(
    sk_B != sk_D ),
    inference(simpl_trail,[status(thm)],['197','203'])).

thf('205',plain,(
    ( k4_xboole_0 @ sk_B @ sk_D )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['195','204'])).

thf('206',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['151','205'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hztmehgxyV
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.28/29.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 29.28/29.50  % Solved by: fo/fo7.sh
% 29.28/29.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.28/29.50  % done 10080 iterations in 29.072s
% 29.28/29.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 29.28/29.50  % SZS output start Refutation
% 29.28/29.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 29.28/29.50  thf(sk_B_type, type, sk_B: $i).
% 29.28/29.50  thf(sk_A_type, type, sk_A: $i).
% 29.28/29.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 29.28/29.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.28/29.50  thf(sk_C_type, type, sk_C: $i).
% 29.28/29.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 29.28/29.50  thf(sk_D_type, type, sk_D: $i).
% 29.28/29.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 29.28/29.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 29.28/29.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 29.28/29.50  thf(t134_zfmisc_1, conjecture,
% 29.28/29.50    (![A:$i,B:$i,C:$i,D:$i]:
% 29.28/29.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 29.28/29.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.28/29.50         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 29.28/29.50  thf(zf_stmt_0, negated_conjecture,
% 29.28/29.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 29.28/29.50        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 29.28/29.50          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.28/29.50            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 29.28/29.50    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 29.28/29.50  thf('0', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf(t125_zfmisc_1, axiom,
% 29.28/29.50    (![A:$i,B:$i,C:$i]:
% 29.28/29.50     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 29.28/29.50         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 29.28/29.50       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 29.28/29.50         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 29.28/29.50  thf('1', plain,
% 29.28/29.50      (![X58 : $i, X60 : $i, X61 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ X61 @ (k4_xboole_0 @ X58 @ X60))
% 29.28/29.50           = (k4_xboole_0 @ (k2_zfmisc_1 @ X61 @ X58) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X61 @ X60)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 29.28/29.50  thf('2', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 29.28/29.50           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 29.28/29.50              (k2_zfmisc_1 @ sk_A @ X0)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['0', '1'])).
% 29.28/29.50  thf('3', plain,
% 29.28/29.50      (![X58 : $i, X59 : $i, X60 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k4_xboole_0 @ X58 @ X60) @ X59)
% 29.28/29.50           = (k4_xboole_0 @ (k2_zfmisc_1 @ X58 @ X59) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X60 @ X59)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 29.28/29.50  thf('4', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_D)
% 29.28/29.50         = (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['2', '3'])).
% 29.28/29.50  thf(t113_zfmisc_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]:
% 29.28/29.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 29.28/29.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 29.28/29.50  thf('5', plain,
% 29.28/29.50      (![X40 : $i, X41 : $i]:
% 29.28/29.50         (((X40) = (k1_xboole_0))
% 29.28/29.50          | ((X41) = (k1_xboole_0))
% 29.28/29.50          | ((k2_zfmisc_1 @ X41 @ X40) != (k1_xboole_0)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 29.28/29.50  thf('6', plain,
% 29.28/29.50      ((((k2_zfmisc_1 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_D) != (k1_xboole_0))
% 29.28/29.50        | ((sk_A) = (k1_xboole_0))
% 29.28/29.50        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 29.28/29.50      inference('sup-', [status(thm)], ['4', '5'])).
% 29.28/29.50  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('8', plain,
% 29.28/29.50      ((((k2_zfmisc_1 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_D) != (k1_xboole_0))
% 29.28/29.50        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 29.28/29.50      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 29.28/29.50  thf('9', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf(t123_zfmisc_1, axiom,
% 29.28/29.50    (![A:$i,B:$i,C:$i,D:$i]:
% 29.28/29.50     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 29.28/29.50       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 29.28/29.50  thf('10', plain,
% 29.28/29.50      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X54 @ X56) @ (k3_xboole_0 @ X55 @ X57))
% 29.28/29.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X54 @ X55) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X56 @ X57)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 29.28/29.50  thf('11', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 29.28/29.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 29.28/29.50              (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['9', '10'])).
% 29.28/29.50  thf('12', plain,
% 29.28/29.50      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X54 @ X56) @ (k3_xboole_0 @ X55 @ X57))
% 29.28/29.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X54 @ X55) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X56 @ X57)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 29.28/29.50  thf('13', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 29.28/29.50           = (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_C) @ 
% 29.28/29.50              (k3_xboole_0 @ X0 @ sk_D)))),
% 29.28/29.50      inference('demod', [status(thm)], ['11', '12'])).
% 29.28/29.50  thf('14', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf(t120_zfmisc_1, axiom,
% 29.28/29.50    (![A:$i,B:$i,C:$i]:
% 29.28/29.50     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 29.28/29.50         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 29.28/29.50       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 29.28/29.50         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 29.28/29.50  thf('15', plain,
% 29.28/29.50      (![X46 : $i, X47 : $i, X48 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k2_xboole_0 @ X46 @ X48) @ X47)
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X46 @ X47) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X48 @ X47)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 29.28/29.50  thf('16', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B)
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 29.28/29.50              (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['14', '15'])).
% 29.28/29.50  thf('17', plain,
% 29.28/29.50      (![X46 : $i, X48 : $i, X49 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ X49 @ (k2_xboole_0 @ X46 @ X48))
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X49 @ X46) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X49 @ X48)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 29.28/29.50  thf('18', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_D))
% 29.28/29.50         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 29.28/29.50      inference('sup+', [status(thm)], ['16', '17'])).
% 29.28/29.50  thf('19', plain,
% 29.28/29.50      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X54 @ X56) @ (k3_xboole_0 @ X55 @ X57))
% 29.28/29.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X54 @ X55) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X56 @ X57)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 29.28/29.50  thf('20', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ X1) @ 
% 29.28/29.50           (k3_xboole_0 @ sk_B @ X0))
% 29.28/29.50           = (k3_xboole_0 @ 
% 29.28/29.50              (k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_D)) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X1 @ X0)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['18', '19'])).
% 29.28/29.50  thf('21', plain,
% 29.28/29.50      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X54 @ X56) @ (k3_xboole_0 @ X55 @ X57))
% 29.28/29.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X54 @ X55) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X56 @ X57)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 29.28/29.50  thf('22', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ X1) @ 
% 29.28/29.50           (k3_xboole_0 @ sk_B @ X0))
% 29.28/29.50           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X1) @ 
% 29.28/29.50              (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_D) @ X0)))),
% 29.28/29.50      inference('demod', [status(thm)], ['20', '21'])).
% 29.28/29.50  thf('23', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_C) @ 
% 29.28/29.50         (k3_xboole_0 @ sk_B @ sk_D))
% 29.28/29.50         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 29.28/29.50            (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_D) @ sk_B)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['13', '22'])).
% 29.28/29.50  thf(commutativity_k3_xboole_0, axiom,
% 29.28/29.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 29.28/29.50  thf('24', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.28/29.50  thf(t21_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 29.28/29.50  thf('25', plain,
% 29.28/29.50      (![X19 : $i, X20 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (X19))),
% 29.28/29.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 29.28/29.50  thf('26', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.28/29.50  thf('27', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.28/29.50  thf('28', plain,
% 29.28/29.50      (![X19 : $i, X20 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (X19))),
% 29.28/29.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 29.28/29.50  thf('29', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 29.28/29.50         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 29.28/29.50      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 29.28/29.50  thf('30', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf(t117_zfmisc_1, axiom,
% 29.28/29.50    (![A:$i,B:$i,C:$i]:
% 29.28/29.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 29.28/29.50          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 29.28/29.50            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 29.28/29.50          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 29.28/29.50  thf('31', plain,
% 29.28/29.50      (![X43 : $i, X44 : $i, X45 : $i]:
% 29.28/29.50         (((X43) = (k1_xboole_0))
% 29.28/29.50          | (r1_tarski @ X44 @ X45)
% 29.28/29.50          | ~ (r1_tarski @ (k2_zfmisc_1 @ X44 @ X43) @ 
% 29.28/29.50               (k2_zfmisc_1 @ X45 @ X43)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 29.28/29.50  thf('32', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 29.28/29.50             (k2_zfmisc_1 @ X0 @ sk_B))
% 29.28/29.50          | (r1_tarski @ sk_A @ X0)
% 29.28/29.50          | ((sk_B) = (k1_xboole_0)))),
% 29.28/29.50      inference('sup-', [status(thm)], ['30', '31'])).
% 29.28/29.50  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('34', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 29.28/29.50             (k2_zfmisc_1 @ X0 @ sk_B))
% 29.28/29.50          | (r1_tarski @ sk_A @ X0))),
% 29.28/29.50      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 29.28/29.50  thf('35', plain,
% 29.28/29.50      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 29.28/29.50           (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))
% 29.28/29.50        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 29.28/29.50      inference('sup-', [status(thm)], ['29', '34'])).
% 29.28/29.50  thf(idempotence_k3_xboole_0, axiom,
% 29.28/29.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 29.28/29.50  thf('36', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 29.28/29.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 29.28/29.50  thf(t111_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i,C:$i]:
% 29.28/29.50     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 29.28/29.50       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 29.28/29.50  thf('37', plain,
% 29.28/29.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ (k3_xboole_0 @ X10 @ X12) @ (k3_xboole_0 @ X11 @ X12))
% 29.28/29.50           = (k3_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12))),
% 29.28/29.50      inference('cnf', [status(esa)], [t111_xboole_1])).
% 29.28/29.50  thf('38', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 29.28/29.50           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['36', '37'])).
% 29.28/29.50  thf('39', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.28/29.50  thf('40', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 29.28/29.50           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 29.28/29.50      inference('demod', [status(thm)], ['38', '39'])).
% 29.28/29.50  thf(t49_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i,C:$i]:
% 29.28/29.50     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 29.28/29.50       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 29.28/29.50  thf('41', plain,
% 29.28/29.50      (![X36 : $i, X37 : $i, X38 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X36 @ (k4_xboole_0 @ X37 @ X38))
% 29.28/29.50           = (k4_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ X38))),
% 29.28/29.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 29.28/29.50  thf('42', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 29.28/29.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 29.28/29.50  thf(t100_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]:
% 29.28/29.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 29.28/29.50  thf('43', plain,
% 29.28/29.50      (![X8 : $i, X9 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ X8 @ X9)
% 29.28/29.50           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 29.28/29.50  thf('44', plain,
% 29.28/29.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['42', '43'])).
% 29.28/29.50  thf('45', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 29.28/29.50           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 29.28/29.50      inference('demod', [status(thm)], ['40', '41', '44'])).
% 29.28/29.50  thf('46', plain,
% 29.28/29.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['42', '43'])).
% 29.28/29.50  thf(t4_boole, axiom,
% 29.28/29.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 29.28/29.50  thf('47', plain,
% 29.28/29.50      (![X39 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X39) = (k1_xboole_0))),
% 29.28/29.50      inference('cnf', [status(esa)], [t4_boole])).
% 29.28/29.50  thf(l32_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]:
% 29.28/29.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 29.28/29.50  thf('48', plain,
% 29.28/29.50      (![X3 : $i, X4 : $i]:
% 29.28/29.50         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 29.28/29.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 29.28/29.50  thf('49', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 29.28/29.50      inference('sup-', [status(thm)], ['47', '48'])).
% 29.28/29.50  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 29.28/29.50      inference('simplify', [status(thm)], ['49'])).
% 29.28/29.50  thf(t12_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]:
% 29.28/29.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 29.28/29.50  thf('51', plain,
% 29.28/29.50      (![X13 : $i, X14 : $i]:
% 29.28/29.50         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 29.28/29.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 29.28/29.50  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.28/29.50      inference('sup-', [status(thm)], ['50', '51'])).
% 29.28/29.50  thf(t40_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]:
% 29.28/29.50     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 29.28/29.50  thf('53', plain,
% 29.28/29.50      (![X30 : $i, X31 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ (k2_xboole_0 @ X30 @ X31) @ X31)
% 29.28/29.50           = (k4_xboole_0 @ X30 @ X31))),
% 29.28/29.50      inference('cnf', [status(esa)], [t40_xboole_1])).
% 29.28/29.50  thf('54', plain,
% 29.28/29.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['52', '53'])).
% 29.28/29.50  thf('55', plain,
% 29.28/29.50      (![X39 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X39) = (k1_xboole_0))),
% 29.28/29.50      inference('cnf', [status(esa)], [t4_boole])).
% 29.28/29.50  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 29.28/29.50      inference('demod', [status(thm)], ['54', '55'])).
% 29.28/29.50  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['46', '56'])).
% 29.28/29.50  thf(t2_boole, axiom,
% 29.28/29.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 29.28/29.50  thf('58', plain,
% 29.28/29.50      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 29.28/29.50      inference('cnf', [status(esa)], [t2_boole])).
% 29.28/29.50  thf('59', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['57', '58'])).
% 29.28/29.50  thf('60', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 29.28/29.50      inference('demod', [status(thm)], ['45', '59'])).
% 29.28/29.50  thf('61', plain,
% 29.28/29.50      (![X36 : $i, X37 : $i, X38 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X36 @ (k4_xboole_0 @ X37 @ X38))
% 29.28/29.50           = (k4_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ X38))),
% 29.28/29.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 29.28/29.50  thf('62', plain,
% 29.28/29.50      (![X3 : $i, X4 : $i]:
% 29.28/29.50         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 29.28/29.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 29.28/29.50  thf('63', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.28/29.50         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 29.28/29.50          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 29.28/29.50      inference('sup-', [status(thm)], ['61', '62'])).
% 29.28/29.50  thf('64', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         (((k1_xboole_0) != (k1_xboole_0))
% 29.28/29.50          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 29.28/29.50      inference('sup-', [status(thm)], ['60', '63'])).
% 29.28/29.50  thf('65', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 29.28/29.50      inference('simplify', [status(thm)], ['64'])).
% 29.28/29.50  thf('66', plain,
% 29.28/29.50      (![X13 : $i, X14 : $i]:
% 29.28/29.50         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 29.28/29.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 29.28/29.50  thf('67', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 29.28/29.50      inference('sup-', [status(thm)], ['65', '66'])).
% 29.28/29.50  thf('68', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('69', plain,
% 29.28/29.50      (![X46 : $i, X47 : $i, X48 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k2_xboole_0 @ X46 @ X48) @ X47)
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X46 @ X47) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X48 @ X47)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 29.28/29.50  thf('70', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['68', '69'])).
% 29.28/29.50  thf('71', plain,
% 29.28/29.50      (![X19 : $i, X20 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (X19))),
% 29.28/29.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 29.28/29.50  thf('72', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 29.28/29.50           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))
% 29.28/29.50           = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('sup+', [status(thm)], ['70', '71'])).
% 29.28/29.50  thf('73', plain,
% 29.28/29.50      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X54 @ X56) @ (k3_xboole_0 @ X55 @ X57))
% 29.28/29.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X54 @ X55) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X56 @ X57)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 29.28/29.50  thf('74', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 29.28/29.50           (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('demod', [status(thm)], ['72', '73'])).
% 29.28/29.50  thf('75', plain,
% 29.28/29.50      (![X46 : $i, X47 : $i, X48 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k2_xboole_0 @ X46 @ X48) @ X47)
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X46 @ X47) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X48 @ X47)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 29.28/29.50  thf('76', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ 
% 29.28/29.50           (k2_xboole_0 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X1)) @ X0) @ 
% 29.28/29.50           (k3_xboole_0 @ sk_D @ sk_B))
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B))))),
% 29.28/29.50      inference('sup+', [status(thm)], ['74', '75'])).
% 29.28/29.50  thf('77', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 29.28/29.50         = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 29.28/29.50            (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))))),
% 29.28/29.50      inference('sup+', [status(thm)], ['67', '76'])).
% 29.28/29.50  thf('78', plain,
% 29.28/29.50      (![X46 : $i, X48 : $i, X49 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ X49 @ (k2_xboole_0 @ X46 @ X48))
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X49 @ X46) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X49 @ X48)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 29.28/29.50  thf(t22_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 29.28/29.50  thf('79', plain,
% 29.28/29.50      (![X21 : $i, X22 : $i]:
% 29.28/29.50         ((k2_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)) = (X21))),
% 29.28/29.50      inference('cnf', [status(esa)], [t22_xboole_1])).
% 29.28/29.50  thf('80', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 29.28/29.50         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('demod', [status(thm)], ['77', '78', '79'])).
% 29.28/29.50  thf('81', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 29.28/29.50      inference('demod', [status(thm)], ['54', '55'])).
% 29.28/29.50  thf('82', plain,
% 29.28/29.50      (![X3 : $i, X4 : $i]:
% 29.28/29.50         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 29.28/29.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 29.28/29.50  thf('83', plain,
% 29.28/29.50      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 29.28/29.50      inference('sup-', [status(thm)], ['81', '82'])).
% 29.28/29.50  thf('84', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 29.28/29.50      inference('simplify', [status(thm)], ['83'])).
% 29.28/29.50  thf('85', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A))),
% 29.28/29.50      inference('demod', [status(thm)], ['35', '80', '84'])).
% 29.28/29.50  thf('86', plain,
% 29.28/29.50      (![X13 : $i, X14 : $i]:
% 29.28/29.50         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 29.28/29.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 29.28/29.50  thf('87', plain,
% 29.28/29.50      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A))
% 29.28/29.50         = (k3_xboole_0 @ sk_C @ sk_A))),
% 29.28/29.50      inference('sup-', [status(thm)], ['85', '86'])).
% 29.28/29.50  thf('88', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.28/29.50  thf('89', plain,
% 29.28/29.50      (![X21 : $i, X22 : $i]:
% 29.28/29.50         ((k2_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)) = (X21))),
% 29.28/29.50      inference('cnf', [status(esa)], [t22_xboole_1])).
% 29.28/29.50  thf('90', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['88', '89'])).
% 29.28/29.50  thf('91', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 29.28/29.50      inference('demod', [status(thm)], ['87', '90'])).
% 29.28/29.50  thf('92', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 29.28/29.50      inference('sup-', [status(thm)], ['65', '66'])).
% 29.28/29.50  thf('93', plain, (((k2_xboole_0 @ sk_A @ sk_C) = (sk_C))),
% 29.28/29.50      inference('sup+', [status(thm)], ['91', '92'])).
% 29.28/29.50  thf('94', plain,
% 29.28/29.50      (![X46 : $i, X48 : $i, X49 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ X49 @ (k2_xboole_0 @ X46 @ X48))
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X49 @ X46) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X49 @ X48)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 29.28/29.50  thf('95', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['68', '69'])).
% 29.28/29.50  thf('96', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 29.28/29.50         = (k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_D @ sk_B)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['94', '95'])).
% 29.28/29.50  thf('97', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('98', plain,
% 29.28/29.50      (![X43 : $i, X44 : $i, X45 : $i]:
% 29.28/29.50         (((X43) = (k1_xboole_0))
% 29.28/29.50          | (r1_tarski @ X44 @ X45)
% 29.28/29.50          | ~ (r1_tarski @ (k2_zfmisc_1 @ X44 @ X43) @ 
% 29.28/29.50               (k2_zfmisc_1 @ X45 @ X43)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 29.28/29.50  thf('99', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 29.28/29.50             (k2_zfmisc_1 @ sk_C @ sk_D))
% 29.28/29.50          | (r1_tarski @ X0 @ sk_A)
% 29.28/29.50          | ((sk_B) = (k1_xboole_0)))),
% 29.28/29.50      inference('sup-', [status(thm)], ['97', '98'])).
% 29.28/29.50  thf('100', plain, (((sk_B) != (k1_xboole_0))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('101', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 29.28/29.50             (k2_zfmisc_1 @ sk_C @ sk_D))
% 29.28/29.50          | (r1_tarski @ X0 @ sk_A))),
% 29.28/29.50      inference('simplify_reflect-', [status(thm)], ['99', '100'])).
% 29.28/29.50  thf('102', plain,
% 29.28/29.50      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_D @ sk_B)) @ 
% 29.28/29.50           (k2_zfmisc_1 @ sk_C @ sk_D))
% 29.28/29.50        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_A))),
% 29.28/29.50      inference('sup-', [status(thm)], ['96', '101'])).
% 29.28/29.50  thf('103', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 29.28/29.50      inference('simplify', [status(thm)], ['83'])).
% 29.28/29.50  thf('104', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('105', plain,
% 29.28/29.50      (![X46 : $i, X48 : $i, X49 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ X49 @ (k2_xboole_0 @ X46 @ X48))
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X49 @ X46) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X49 @ X48)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 29.28/29.50  thf('106', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 29.28/29.50              (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['104', '105'])).
% 29.28/29.50  thf('107', plain,
% 29.28/29.50      (![X46 : $i, X47 : $i, X48 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k2_xboole_0 @ X46 @ X48) @ X47)
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X46 @ X47) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X48 @ X47)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 29.28/29.50  thf('108', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_D)
% 29.28/29.50         = (k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_D @ sk_B)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['106', '107'])).
% 29.28/29.50  thf('109', plain,
% 29.28/29.50      (![X43 : $i, X44 : $i, X45 : $i]:
% 29.28/29.50         (((X43) = (k1_xboole_0))
% 29.28/29.50          | (r1_tarski @ X44 @ X45)
% 29.28/29.50          | ~ (r1_tarski @ (k2_zfmisc_1 @ X43 @ X44) @ 
% 29.28/29.50               (k2_zfmisc_1 @ X43 @ X45)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 29.28/29.50  thf('110', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         (~ (r1_tarski @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_D) @ 
% 29.28/29.50             (k2_zfmisc_1 @ sk_A @ X0))
% 29.28/29.50          | (r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ X0)
% 29.28/29.50          | ((sk_A) = (k1_xboole_0)))),
% 29.28/29.50      inference('sup-', [status(thm)], ['108', '109'])).
% 29.28/29.50  thf('111', plain, (((sk_A) != (k1_xboole_0))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('112', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         (~ (r1_tarski @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_D) @ 
% 29.28/29.50             (k2_zfmisc_1 @ sk_A @ X0))
% 29.28/29.50          | (r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ X0))),
% 29.28/29.50      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 29.28/29.50  thf('113', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_D)
% 29.28/29.50         = (k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_D @ sk_B)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['106', '107'])).
% 29.28/29.50  thf('114', plain,
% 29.28/29.50      (![X46 : $i, X48 : $i, X49 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ X49 @ (k2_xboole_0 @ X46 @ X48))
% 29.28/29.50           = (k2_xboole_0 @ (k2_zfmisc_1 @ X49 @ X46) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X49 @ X48)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 29.28/29.50  thf('115', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ sk_A @ 
% 29.28/29.50           (k2_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_B) @ X0))
% 29.28/29.50           = (k2_xboole_0 @ 
% 29.28/29.50              (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_D) @ 
% 29.28/29.50              (k2_zfmisc_1 @ sk_A @ X0)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['113', '114'])).
% 29.28/29.50  thf('116', plain,
% 29.28/29.50      (![X19 : $i, X20 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (X19))),
% 29.28/29.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 29.28/29.50  thf('117', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_D) @ 
% 29.28/29.50           (k2_zfmisc_1 @ sk_A @ 
% 29.28/29.50            (k2_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_B) @ X0)))
% 29.28/29.50           = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_D))),
% 29.28/29.50      inference('sup+', [status(thm)], ['115', '116'])).
% 29.28/29.50  thf('118', plain,
% 29.28/29.50      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k3_xboole_0 @ X54 @ X56) @ (k3_xboole_0 @ X55 @ X57))
% 29.28/29.50           = (k3_xboole_0 @ (k2_zfmisc_1 @ X54 @ X55) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X56 @ X57)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 29.28/29.50  thf('119', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.28/29.50  thf('120', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1))
% 29.28/29.50           = (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['118', '119'])).
% 29.28/29.50  thf('121', plain,
% 29.28/29.50      (![X19 : $i, X20 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (X19))),
% 29.28/29.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 29.28/29.50  thf('122', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.28/29.50  thf('123', plain,
% 29.28/29.50      (![X19 : $i, X20 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (X19))),
% 29.28/29.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 29.28/29.50  thf('124', plain,
% 29.28/29.50      (![X19 : $i, X20 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (X19))),
% 29.28/29.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 29.28/29.50  thf(t16_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i,C:$i]:
% 29.28/29.50     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 29.28/29.50       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 29.28/29.50  thf('125', plain,
% 29.28/29.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17)
% 29.28/29.50           = (k3_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t16_xboole_1])).
% 29.28/29.50  thf('126', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X0 @ X1)
% 29.28/29.50           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['124', '125'])).
% 29.28/29.50  thf('127', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 29.28/29.50           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['123', '126'])).
% 29.28/29.50  thf('128', plain,
% 29.28/29.50      (![X19 : $i, X20 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (X19))),
% 29.28/29.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 29.28/29.50  thf('129', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 29.28/29.50           = (X1))),
% 29.28/29.50      inference('demod', [status(thm)], ['127', '128'])).
% 29.28/29.50  thf('130', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_A @ sk_D)
% 29.28/29.50         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_D))),
% 29.28/29.50      inference('demod', [status(thm)], ['117', '120', '121', '122', '129'])).
% 29.28/29.50  thf('131', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 29.28/29.50             (k2_zfmisc_1 @ sk_A @ X0))
% 29.28/29.50          | (r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ X0))),
% 29.28/29.50      inference('demod', [status(thm)], ['112', '130'])).
% 29.28/29.50  thf('132', plain, ((r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_D)),
% 29.28/29.50      inference('sup-', [status(thm)], ['103', '131'])).
% 29.28/29.50  thf('133', plain,
% 29.28/29.50      (![X13 : $i, X14 : $i]:
% 29.28/29.50         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 29.28/29.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 29.28/29.50  thf('134', plain,
% 29.28/29.50      (((k2_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_D) = (sk_D))),
% 29.28/29.50      inference('sup-', [status(thm)], ['132', '133'])).
% 29.28/29.50  thf('135', plain,
% 29.28/29.50      (![X19 : $i, X20 : $i]:
% 29.28/29.50         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (X19))),
% 29.28/29.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 29.28/29.50  thf('136', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['88', '89'])).
% 29.28/29.50  thf('137', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 29.28/29.50           = (k2_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('sup+', [status(thm)], ['135', '136'])).
% 29.28/29.50  thf('138', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 29.28/29.50      inference('demod', [status(thm)], ['134', '137'])).
% 29.28/29.50  thf('139', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 29.28/29.50      inference('simplify', [status(thm)], ['83'])).
% 29.28/29.50  thf('140', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_A)),
% 29.28/29.50      inference('demod', [status(thm)], ['102', '138', '139'])).
% 29.28/29.50  thf('141', plain,
% 29.28/29.50      (![X13 : $i, X14 : $i]:
% 29.28/29.50         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 29.28/29.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 29.28/29.50  thf('142', plain,
% 29.28/29.50      (((k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_A) = (sk_A))),
% 29.28/29.50      inference('sup-', [status(thm)], ['140', '141'])).
% 29.28/29.50  thf('143', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 29.28/29.50           = (k2_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('sup+', [status(thm)], ['135', '136'])).
% 29.28/29.50  thf('144', plain, (((k2_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 29.28/29.50      inference('demod', [status(thm)], ['142', '143'])).
% 29.28/29.50  thf('145', plain, (((sk_C) = (sk_A))),
% 29.28/29.50      inference('sup+', [status(thm)], ['93', '144'])).
% 29.28/29.50  thf('146', plain,
% 29.28/29.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['42', '43'])).
% 29.28/29.50  thf('147', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['46', '56'])).
% 29.28/29.50  thf('148', plain,
% 29.28/29.50      (![X41 : $i, X42 : $i]:
% 29.28/29.50         (((k2_zfmisc_1 @ X41 @ X42) = (k1_xboole_0))
% 29.28/29.50          | ((X41) != (k1_xboole_0)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 29.28/29.50  thf('149', plain,
% 29.28/29.50      (![X42 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X42) = (k1_xboole_0))),
% 29.28/29.50      inference('simplify', [status(thm)], ['148'])).
% 29.28/29.50  thf('150', plain,
% 29.28/29.50      ((((k1_xboole_0) != (k1_xboole_0))
% 29.28/29.50        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 29.28/29.50      inference('demod', [status(thm)], ['8', '145', '146', '147', '149'])).
% 29.28/29.50  thf('151', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 29.28/29.50      inference('simplify', [status(thm)], ['150'])).
% 29.28/29.50  thf('152', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 29.28/29.50      inference('demod', [status(thm)], ['134', '137'])).
% 29.28/29.50  thf('153', plain,
% 29.28/29.50      (![X30 : $i, X31 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ (k2_xboole_0 @ X30 @ X31) @ X31)
% 29.28/29.50           = (k4_xboole_0 @ X30 @ X31))),
% 29.28/29.50      inference('cnf', [status(esa)], [t40_xboole_1])).
% 29.28/29.50  thf(t32_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]:
% 29.28/29.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 29.28/29.50       ( ( A ) = ( B ) ) ))).
% 29.28/29.50  thf('154', plain,
% 29.28/29.50      (![X24 : $i, X25 : $i]:
% 29.28/29.50         (((X25) = (X24))
% 29.28/29.50          | ((k4_xboole_0 @ X25 @ X24) != (k4_xboole_0 @ X24 @ X25)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t32_xboole_1])).
% 29.28/29.50  thf('155', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 29.28/29.50            != (k4_xboole_0 @ X1 @ X0))
% 29.28/29.50          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 29.28/29.50      inference('sup-', [status(thm)], ['153', '154'])).
% 29.28/29.50  thf('156', plain,
% 29.28/29.50      ((((k4_xboole_0 @ sk_B @ sk_D) != (k4_xboole_0 @ sk_D @ sk_B))
% 29.28/29.50        | ((sk_B) = (k2_xboole_0 @ sk_D @ sk_B)))),
% 29.28/29.50      inference('sup-', [status(thm)], ['152', '155'])).
% 29.28/29.50  thf('157', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 29.28/29.50      inference('demod', [status(thm)], ['134', '137'])).
% 29.28/29.50  thf('158', plain,
% 29.28/29.50      ((((k4_xboole_0 @ sk_B @ sk_D) != (k4_xboole_0 @ sk_D @ sk_B))
% 29.28/29.50        | ((sk_B) = (sk_D)))),
% 29.28/29.50      inference('demod', [status(thm)], ['156', '157'])).
% 29.28/29.50  thf('159', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 29.28/29.50      inference('demod', [status(thm)], ['134', '137'])).
% 29.28/29.50  thf(l98_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]:
% 29.28/29.50     ( ( k5_xboole_0 @ A @ B ) =
% 29.28/29.50       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 29.28/29.50  thf('160', plain,
% 29.28/29.50      (![X6 : $i, X7 : $i]:
% 29.28/29.50         ((k5_xboole_0 @ X6 @ X7)
% 29.28/29.50           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 29.28/29.50      inference('cnf', [status(esa)], [l98_xboole_1])).
% 29.28/29.50  thf('161', plain,
% 29.28/29.50      (((k5_xboole_0 @ sk_D @ sk_B)
% 29.28/29.50         = (k4_xboole_0 @ sk_D @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['159', '160'])).
% 29.28/29.50  thf(t47_xboole_1, axiom,
% 29.28/29.50    (![A:$i,B:$i]:
% 29.28/29.50     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 29.28/29.50  thf('162', plain,
% 29.28/29.50      (![X34 : $i, X35 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ X34 @ (k3_xboole_0 @ X34 @ X35))
% 29.28/29.50           = (k4_xboole_0 @ X34 @ X35))),
% 29.28/29.50      inference('cnf', [status(esa)], [t47_xboole_1])).
% 29.28/29.50  thf('163', plain,
% 29.28/29.50      (((k5_xboole_0 @ sk_D @ sk_B) = (k4_xboole_0 @ sk_D @ sk_B))),
% 29.28/29.50      inference('demod', [status(thm)], ['161', '162'])).
% 29.28/29.50  thf('164', plain,
% 29.28/29.50      ((((k4_xboole_0 @ sk_B @ sk_D) != (k5_xboole_0 @ sk_D @ sk_B))
% 29.28/29.50        | ((sk_B) = (sk_D)))),
% 29.28/29.50      inference('demod', [status(thm)], ['158', '163'])).
% 29.28/29.50  thf('165', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('166', plain,
% 29.28/29.50      (![X58 : $i, X60 : $i, X61 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ X61 @ (k4_xboole_0 @ X58 @ X60))
% 29.28/29.50           = (k4_xboole_0 @ (k2_zfmisc_1 @ X61 @ X58) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X61 @ X60)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 29.28/29.50  thf('167', plain,
% 29.28/29.50      (![X0 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 29.28/29.50           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 29.28/29.50              (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['165', '166'])).
% 29.28/29.50  thf('168', plain,
% 29.28/29.50      (![X58 : $i, X59 : $i, X60 : $i]:
% 29.28/29.50         ((k2_zfmisc_1 @ (k4_xboole_0 @ X58 @ X60) @ X59)
% 29.28/29.50           = (k4_xboole_0 @ (k2_zfmisc_1 @ X58 @ X59) @ 
% 29.28/29.50              (k2_zfmisc_1 @ X60 @ X59)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 29.28/29.50  thf('169', plain,
% 29.28/29.50      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D)
% 29.28/29.50         = (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['167', '168'])).
% 29.28/29.50  thf('170', plain,
% 29.28/29.50      (![X40 : $i, X41 : $i]:
% 29.28/29.50         (((X40) = (k1_xboole_0))
% 29.28/29.50          | ((X41) = (k1_xboole_0))
% 29.28/29.50          | ((k2_zfmisc_1 @ X41 @ X40) != (k1_xboole_0)))),
% 29.28/29.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 29.28/29.50  thf('171', plain,
% 29.28/29.50      ((((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D) != (k1_xboole_0))
% 29.28/29.50        | ((sk_A) = (k1_xboole_0))
% 29.28/29.50        | ((k4_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 29.28/29.50      inference('sup-', [status(thm)], ['169', '170'])).
% 29.28/29.50  thf('172', plain, (((sk_A) != (k1_xboole_0))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('173', plain,
% 29.28/29.50      ((((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D) != (k1_xboole_0))
% 29.28/29.50        | ((k4_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 29.28/29.50      inference('simplify_reflect-', [status(thm)], ['171', '172'])).
% 29.28/29.50  thf('174', plain,
% 29.28/29.50      (((k5_xboole_0 @ sk_D @ sk_B) = (k4_xboole_0 @ sk_D @ sk_B))),
% 29.28/29.50      inference('demod', [status(thm)], ['161', '162'])).
% 29.28/29.50  thf('175', plain,
% 29.28/29.50      ((((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D) != (k1_xboole_0))
% 29.28/29.50        | ((k5_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 29.28/29.50      inference('demod', [status(thm)], ['173', '174'])).
% 29.28/29.50  thf('176', plain, (((k2_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 29.28/29.50      inference('demod', [status(thm)], ['142', '143'])).
% 29.28/29.50  thf('177', plain,
% 29.28/29.50      (![X6 : $i, X7 : $i]:
% 29.28/29.50         ((k5_xboole_0 @ X6 @ X7)
% 29.28/29.50           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 29.28/29.50      inference('cnf', [status(esa)], [l98_xboole_1])).
% 29.28/29.50  thf('178', plain,
% 29.28/29.50      (((k5_xboole_0 @ sk_A @ sk_C)
% 29.28/29.50         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C)))),
% 29.28/29.50      inference('sup+', [status(thm)], ['176', '177'])).
% 29.28/29.50  thf('179', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.28/29.50  thf('180', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.28/29.50  thf('181', plain,
% 29.28/29.50      (![X34 : $i, X35 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ X34 @ (k3_xboole_0 @ X34 @ X35))
% 29.28/29.50           = (k4_xboole_0 @ X34 @ X35))),
% 29.28/29.50      inference('cnf', [status(esa)], [t47_xboole_1])).
% 29.28/29.50  thf('182', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 29.28/29.50           = (k4_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('sup+', [status(thm)], ['180', '181'])).
% 29.28/29.50  thf('183', plain,
% 29.28/29.50      (((k5_xboole_0 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 29.28/29.50      inference('demod', [status(thm)], ['178', '179', '182'])).
% 29.28/29.50  thf('184', plain,
% 29.28/29.50      ((((k2_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_D) != (k1_xboole_0))
% 29.28/29.50        | ((k5_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 29.28/29.50      inference('demod', [status(thm)], ['175', '183'])).
% 29.28/29.50  thf('185', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A))),
% 29.28/29.50      inference('demod', [status(thm)], ['35', '80', '84'])).
% 29.28/29.50  thf('186', plain,
% 29.28/29.50      (![X3 : $i, X5 : $i]:
% 29.28/29.50         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 29.28/29.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 29.28/29.50  thf('187', plain,
% 29.28/29.50      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0))),
% 29.28/29.50      inference('sup-', [status(thm)], ['185', '186'])).
% 29.28/29.50  thf('188', plain,
% 29.28/29.50      (![X0 : $i, X1 : $i]:
% 29.28/29.50         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 29.28/29.50           = (k4_xboole_0 @ X0 @ X1))),
% 29.28/29.50      inference('sup+', [status(thm)], ['180', '181'])).
% 29.28/29.50  thf('189', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 29.28/29.50      inference('demod', [status(thm)], ['187', '188'])).
% 29.28/29.50  thf('190', plain,
% 29.28/29.50      (((k5_xboole_0 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 29.28/29.50      inference('demod', [status(thm)], ['178', '179', '182'])).
% 29.28/29.50  thf('191', plain, (((k5_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 29.28/29.50      inference('sup+', [status(thm)], ['189', '190'])).
% 29.28/29.50  thf('192', plain,
% 29.28/29.50      (![X42 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X42) = (k1_xboole_0))),
% 29.28/29.50      inference('simplify', [status(thm)], ['148'])).
% 29.28/29.50  thf('193', plain,
% 29.28/29.50      ((((k1_xboole_0) != (k1_xboole_0))
% 29.28/29.50        | ((k5_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 29.28/29.50      inference('demod', [status(thm)], ['184', '191', '192'])).
% 29.28/29.50  thf('194', plain, (((k5_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 29.28/29.50      inference('simplify', [status(thm)], ['193'])).
% 29.28/29.50  thf('195', plain,
% 29.28/29.50      ((((k4_xboole_0 @ sk_B @ sk_D) != (k1_xboole_0)) | ((sk_B) = (sk_D)))),
% 29.28/29.50      inference('demod', [status(thm)], ['164', '194'])).
% 29.28/29.50  thf('196', plain, ((((sk_A) != (sk_C)) | ((sk_B) != (sk_D)))),
% 29.28/29.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.28/29.50  thf('197', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 29.28/29.50      inference('split', [status(esa)], ['196'])).
% 29.28/29.50  thf('198', plain, (((sk_C) = (sk_A))),
% 29.28/29.50      inference('sup+', [status(thm)], ['93', '144'])).
% 29.28/29.50  thf('199', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 29.28/29.50      inference('split', [status(esa)], ['196'])).
% 29.28/29.50  thf('200', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 29.28/29.50      inference('sup-', [status(thm)], ['198', '199'])).
% 29.28/29.50  thf('201', plain, ((((sk_A) = (sk_C)))),
% 29.28/29.50      inference('simplify', [status(thm)], ['200'])).
% 29.28/29.50  thf('202', plain, (~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C)))),
% 29.28/29.50      inference('split', [status(esa)], ['196'])).
% 29.28/29.50  thf('203', plain, (~ (((sk_B) = (sk_D)))),
% 29.28/29.50      inference('sat_resolution*', [status(thm)], ['201', '202'])).
% 29.28/29.50  thf('204', plain, (((sk_B) != (sk_D))),
% 29.28/29.50      inference('simpl_trail', [status(thm)], ['197', '203'])).
% 29.28/29.50  thf('205', plain, (((k4_xboole_0 @ sk_B @ sk_D) != (k1_xboole_0))),
% 29.28/29.50      inference('simplify_reflect-', [status(thm)], ['195', '204'])).
% 29.28/29.50  thf('206', plain, ($false),
% 29.28/29.50      inference('simplify_reflect-', [status(thm)], ['151', '205'])).
% 29.28/29.50  
% 29.28/29.50  % SZS output end Refutation
% 29.28/29.50  
% 29.28/29.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
