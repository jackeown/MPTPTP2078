%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fYlchB1BIN

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:47 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 250 expanded)
%              Number of leaves         :   21 (  81 expanded)
%              Depth                    :   26
%              Number of atoms          :  892 (2450 expanded)
%              Number of equality atoms :  110 ( 274 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t126_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ) )).

thf('5',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X52 @ X54 ) @ ( k2_zfmisc_1 @ X53 @ X55 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X52 @ X53 ) @ X54 ) @ ( k2_zfmisc_1 @ X52 @ ( k4_xboole_0 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) @ k1_xboole_0 )
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X52 @ X54 ) @ ( k2_zfmisc_1 @ X53 @ X55 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X52 @ X53 ) @ X54 ) @ ( k2_zfmisc_1 @ X52 @ ( k4_xboole_0 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k2_zfmisc_1 @ X42 @ X43 )
        = k1_xboole_0 )
      | ( X42 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['15','17','18'])).

thf('20',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('21',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X48 @ X50 ) @ X49 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X48 @ X49 ) @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','26'])).

thf('28',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('30',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X52 @ X54 ) @ ( k2_zfmisc_1 @ X53 @ X55 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X52 @ X53 ) @ X54 ) @ ( k2_zfmisc_1 @ X52 @ ( k4_xboole_0 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X48: $i,X50: $i,X51: $i] :
      ( ( k2_zfmisc_1 @ X51 @ ( k4_xboole_0 @ X48 @ X50 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X51 @ X48 ) @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','40'])).

thf('42',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X42 @ X41 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_C )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_C )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('51',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X42 @ X41 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['48'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k2_zfmisc_1 @ X42 @ X43 )
        = k1_xboole_0 )
      | ( X43 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('62',plain,(
    ! [X42: $i] :
      ( ( k2_zfmisc_1 @ X42 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['60','62'])).

thf('64',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['48'])).

thf('66',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['49','66'])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','67'])).

thf('69',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X52 @ X54 ) @ ( k2_zfmisc_1 @ X53 @ X55 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X52 @ X53 ) @ X54 ) @ ( k2_zfmisc_1 @ X52 @ ( k4_xboole_0 @ X54 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_C @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_C @ X0 ) )
      = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','73'])).

thf('75',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X42 @ X41 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['49','66'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X43: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X43 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('84',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','82','83'])).

thf('85',plain,(
    $false ),
    inference(simplify,[status(thm)],['84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fYlchB1BIN
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.91/2.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.91/2.10  % Solved by: fo/fo7.sh
% 1.91/2.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.10  % done 2357 iterations in 1.652s
% 1.91/2.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.91/2.10  % SZS output start Refutation
% 1.91/2.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.91/2.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.91/2.10  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.91/2.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.91/2.10  thf(sk_C_type, type, sk_C: $i).
% 1.91/2.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.91/2.10  thf(sk_D_type, type, sk_D: $i).
% 1.91/2.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.91/2.10  thf(sk_B_type, type, sk_B: $i).
% 1.91/2.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.91/2.10  thf(t138_zfmisc_1, conjecture,
% 1.91/2.10    (![A:$i,B:$i,C:$i,D:$i]:
% 1.91/2.10     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.91/2.10       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 1.91/2.10         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 1.91/2.10  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.10    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.91/2.10        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.91/2.10          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 1.91/2.10            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 1.91/2.10    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 1.91/2.10  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('1', plain,
% 1.91/2.10      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf(l32_xboole_1, axiom,
% 1.91/2.10    (![A:$i,B:$i]:
% 1.91/2.10     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.91/2.10  thf('2', plain,
% 1.91/2.10      (![X1 : $i, X3 : $i]:
% 1.91/2.10         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 1.91/2.10      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.91/2.10  thf('3', plain,
% 1.91/2.10      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.91/2.10         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['1', '2'])).
% 1.91/2.10  thf('4', plain,
% 1.91/2.10      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.91/2.10         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['1', '2'])).
% 1.91/2.10  thf(t126_zfmisc_1, axiom,
% 1.91/2.10    (![A:$i,B:$i,C:$i,D:$i]:
% 1.91/2.10     ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =
% 1.91/2.10       ( k2_xboole_0 @
% 1.91/2.10         ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ 
% 1.91/2.10         ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ))).
% 1.91/2.10  thf('5', plain,
% 1.91/2.10      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ (k2_zfmisc_1 @ X52 @ X54) @ (k2_zfmisc_1 @ X53 @ X55))
% 1.91/2.10           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X52 @ X53) @ X54) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X52 @ (k4_xboole_0 @ X54 @ X55))))),
% 1.91/2.10      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.91/2.10  thf(t21_xboole_1, axiom,
% 1.91/2.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.91/2.10  thf('6', plain,
% 1.91/2.10      (![X6 : $i, X7 : $i]:
% 1.91/2.10         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 1.91/2.10      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.91/2.10  thf('7', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.91/2.10         ((k3_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2) @ 
% 1.91/2.10           (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.91/2.10           = (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2))),
% 1.91/2.10      inference('sup+', [status(thm)], ['5', '6'])).
% 1.91/2.10  thf('8', plain,
% 1.91/2.10      (((k3_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) @ 
% 1.91/2.10         k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 1.91/2.10      inference('sup+', [status(thm)], ['4', '7'])).
% 1.91/2.10  thf(t2_boole, axiom,
% 1.91/2.10    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.91/2.10  thf('9', plain,
% 1.91/2.10      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.91/2.10      inference('cnf', [status(esa)], [t2_boole])).
% 1.91/2.10  thf('10', plain,
% 1.91/2.10      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 1.91/2.10      inference('demod', [status(thm)], ['8', '9'])).
% 1.91/2.10  thf('11', plain,
% 1.91/2.10      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.91/2.10      inference('cnf', [status(esa)], [t2_boole])).
% 1.91/2.10  thf(t100_xboole_1, axiom,
% 1.91/2.10    (![A:$i,B:$i]:
% 1.91/2.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.91/2.10  thf('12', plain,
% 1.91/2.10      (![X4 : $i, X5 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ X4 @ X5)
% 1.91/2.10           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.91/2.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.91/2.10  thf('13', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.91/2.10      inference('sup+', [status(thm)], ['11', '12'])).
% 1.91/2.10  thf('14', plain,
% 1.91/2.10      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ (k2_zfmisc_1 @ X52 @ X54) @ (k2_zfmisc_1 @ X53 @ X55))
% 1.91/2.10           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X52 @ X53) @ X54) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X52 @ (k4_xboole_0 @ X54 @ X55))))),
% 1.91/2.10      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.91/2.10  thf('15', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ 
% 1.91/2.10           (k2_zfmisc_1 @ k1_xboole_0 @ X1))
% 1.91/2.10           = (k2_xboole_0 @ 
% 1.91/2.10              (k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X2) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 1.91/2.10      inference('sup+', [status(thm)], ['13', '14'])).
% 1.91/2.10  thf(t113_zfmisc_1, axiom,
% 1.91/2.10    (![A:$i,B:$i]:
% 1.91/2.10     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.91/2.10       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.91/2.10  thf('16', plain,
% 1.91/2.10      (![X42 : $i, X43 : $i]:
% 1.91/2.10         (((k2_zfmisc_1 @ X42 @ X43) = (k1_xboole_0))
% 1.91/2.10          | ((X42) != (k1_xboole_0)))),
% 1.91/2.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.91/2.10  thf('17', plain,
% 1.91/2.10      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['16'])).
% 1.91/2.10  thf('18', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.91/2.10      inference('sup+', [status(thm)], ['11', '12'])).
% 1.91/2.10  thf('19', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((k5_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ k1_xboole_0)
% 1.91/2.10           = (k2_xboole_0 @ 
% 1.91/2.10              (k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X2) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 1.91/2.10      inference('demod', [status(thm)], ['15', '17', '18'])).
% 1.91/2.10  thf('20', plain,
% 1.91/2.10      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['16'])).
% 1.91/2.10  thf(t125_zfmisc_1, axiom,
% 1.91/2.10    (![A:$i,B:$i,C:$i]:
% 1.91/2.10     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 1.91/2.10         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.91/2.10       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.91/2.10         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.91/2.10  thf('21', plain,
% 1.91/2.10      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.91/2.10         ((k2_zfmisc_1 @ (k4_xboole_0 @ X48 @ X50) @ X49)
% 1.91/2.10           = (k4_xboole_0 @ (k2_zfmisc_1 @ X48 @ X49) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X50 @ X49)))),
% 1.91/2.10      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 1.91/2.10  thf('22', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i]:
% 1.91/2.10         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ k1_xboole_0) @ X0)
% 1.91/2.10           = (k4_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ k1_xboole_0))),
% 1.91/2.10      inference('sup+', [status(thm)], ['20', '21'])).
% 1.91/2.10  thf('23', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.91/2.10      inference('sup+', [status(thm)], ['11', '12'])).
% 1.91/2.10  thf('24', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.91/2.10      inference('sup+', [status(thm)], ['11', '12'])).
% 1.91/2.10  thf('25', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i]:
% 1.91/2.10         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ k1_xboole_0) @ X0)
% 1.91/2.10           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ k1_xboole_0))),
% 1.91/2.10      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.91/2.10  thf('26', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((k5_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ k1_xboole_0)
% 1.91/2.10           = (k2_xboole_0 @ 
% 1.91/2.10              (k5_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ k1_xboole_0) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 1.91/2.10      inference('demod', [status(thm)], ['19', '25'])).
% 1.91/2.10  thf('27', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         ((k5_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) @ 
% 1.91/2.10           k1_xboole_0)
% 1.91/2.10           = (k2_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 1.91/2.10              (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 1.91/2.10               (k4_xboole_0 @ sk_B @ X0))))),
% 1.91/2.10      inference('sup+', [status(thm)], ['10', '26'])).
% 1.91/2.10  thf('28', plain,
% 1.91/2.10      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 1.91/2.10      inference('demod', [status(thm)], ['8', '9'])).
% 1.91/2.10  thf(t92_xboole_1, axiom,
% 1.91/2.10    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.91/2.10  thf('29', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 1.91/2.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.91/2.10  thf('30', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 1.91/2.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.91/2.10  thf(idempotence_k3_xboole_0, axiom,
% 1.91/2.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.91/2.10  thf('31', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.91/2.10      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.91/2.10  thf('32', plain,
% 1.91/2.10      (![X4 : $i, X5 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ X4 @ X5)
% 1.91/2.10           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.91/2.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.91/2.10  thf('33', plain,
% 1.91/2.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.91/2.10      inference('sup+', [status(thm)], ['31', '32'])).
% 1.91/2.10  thf('34', plain,
% 1.91/2.10      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ (k2_zfmisc_1 @ X52 @ X54) @ (k2_zfmisc_1 @ X53 @ X55))
% 1.91/2.10           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X52 @ X53) @ X54) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X52 @ (k4_xboole_0 @ X54 @ X55))))),
% 1.91/2.10      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.91/2.10  thf('35', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1))
% 1.91/2.10           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X2) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 1.91/2.10      inference('sup+', [status(thm)], ['33', '34'])).
% 1.91/2.10  thf('36', plain,
% 1.91/2.10      (![X48 : $i, X50 : $i, X51 : $i]:
% 1.91/2.10         ((k2_zfmisc_1 @ X51 @ (k4_xboole_0 @ X48 @ X50))
% 1.91/2.10           = (k4_xboole_0 @ (k2_zfmisc_1 @ X51 @ X48) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X51 @ X50)))),
% 1.91/2.10      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 1.91/2.10  thf('37', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 1.91/2.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.91/2.10  thf('38', plain,
% 1.91/2.10      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['16'])).
% 1.91/2.10  thf('39', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i]:
% 1.91/2.10         ((k2_zfmisc_1 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 1.91/2.10      inference('sup+', [status(thm)], ['37', '38'])).
% 1.91/2.10  thf('40', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((k2_zfmisc_1 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 1.91/2.10           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.91/2.10              (k2_zfmisc_1 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 1.91/2.10      inference('demod', [status(thm)], ['35', '36', '39'])).
% 1.91/2.10  thf('41', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         ((k1_xboole_0)
% 1.91/2.10           = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 1.91/2.10              (k4_xboole_0 @ sk_B @ X0)))),
% 1.91/2.10      inference('demod', [status(thm)], ['27', '28', '29', '30', '40'])).
% 1.91/2.10  thf('42', plain,
% 1.91/2.10      (![X41 : $i, X42 : $i]:
% 1.91/2.10         (((X41) = (k1_xboole_0))
% 1.91/2.10          | ((X42) = (k1_xboole_0))
% 1.91/2.10          | ((k2_zfmisc_1 @ X42 @ X41) != (k1_xboole_0)))),
% 1.91/2.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.91/2.10  thf('43', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         (((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.10          | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 1.91/2.10          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['41', '42'])).
% 1.91/2.10  thf('44', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         (((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 1.91/2.10          | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['43'])).
% 1.91/2.10  thf('45', plain,
% 1.91/2.10      (![X1 : $i, X2 : $i]:
% 1.91/2.10         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 1.91/2.10      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.91/2.10  thf('46', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         (((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.10          | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 1.91/2.10          | (r1_tarski @ sk_B @ X0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['44', '45'])).
% 1.91/2.10  thf('47', plain,
% 1.91/2.10      (![X0 : $i]:
% 1.91/2.10         ((r1_tarski @ sk_B @ X0)
% 1.91/2.10          | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['46'])).
% 1.91/2.10  thf('48', plain,
% 1.91/2.10      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('49', plain,
% 1.91/2.10      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 1.91/2.10      inference('split', [status(esa)], ['48'])).
% 1.91/2.10  thf('50', plain,
% 1.91/2.10      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 1.91/2.10      inference('demod', [status(thm)], ['8', '9'])).
% 1.91/2.10  thf('51', plain,
% 1.91/2.10      (![X41 : $i, X42 : $i]:
% 1.91/2.10         (((X41) = (k1_xboole_0))
% 1.91/2.10          | ((X42) = (k1_xboole_0))
% 1.91/2.10          | ((k2_zfmisc_1 @ X42 @ X41) != (k1_xboole_0)))),
% 1.91/2.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.91/2.10  thf('52', plain,
% 1.91/2.10      ((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.10        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 1.91/2.10        | ((sk_B) = (k1_xboole_0)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['50', '51'])).
% 1.91/2.10  thf('53', plain,
% 1.91/2.10      ((((sk_B) = (k1_xboole_0))
% 1.91/2.10        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['52'])).
% 1.91/2.10  thf('54', plain,
% 1.91/2.10      (![X1 : $i, X2 : $i]:
% 1.91/2.10         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 1.91/2.10      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.91/2.10  thf('55', plain,
% 1.91/2.10      ((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.10        | ((sk_B) = (k1_xboole_0))
% 1.91/2.10        | (r1_tarski @ sk_A @ sk_C))),
% 1.91/2.10      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.10  thf('56', plain, (((r1_tarski @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['55'])).
% 1.91/2.10  thf('57', plain,
% 1.91/2.10      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.91/2.10      inference('split', [status(esa)], ['48'])).
% 1.91/2.10  thf('58', plain,
% 1.91/2.10      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['56', '57'])).
% 1.91/2.10  thf('59', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('60', plain,
% 1.91/2.10      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.91/2.10         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['58', '59'])).
% 1.91/2.10  thf('61', plain,
% 1.91/2.10      (![X42 : $i, X43 : $i]:
% 1.91/2.10         (((k2_zfmisc_1 @ X42 @ X43) = (k1_xboole_0))
% 1.91/2.10          | ((X43) != (k1_xboole_0)))),
% 1.91/2.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.91/2.10  thf('62', plain,
% 1.91/2.10      (![X42 : $i]: ((k2_zfmisc_1 @ X42 @ k1_xboole_0) = (k1_xboole_0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['61'])).
% 1.91/2.10  thf('63', plain,
% 1.91/2.10      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.91/2.10      inference('demod', [status(thm)], ['60', '62'])).
% 1.91/2.10  thf('64', plain, (((r1_tarski @ sk_A @ sk_C))),
% 1.91/2.10      inference('simplify', [status(thm)], ['63'])).
% 1.91/2.10  thf('65', plain,
% 1.91/2.10      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C))),
% 1.91/2.10      inference('split', [status(esa)], ['48'])).
% 1.91/2.10  thf('66', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 1.91/2.10      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 1.91/2.10  thf('67', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 1.91/2.10      inference('simpl_trail', [status(thm)], ['49', '66'])).
% 1.91/2.10  thf('68', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.91/2.10      inference('sup-', [status(thm)], ['47', '67'])).
% 1.91/2.10  thf('69', plain,
% 1.91/2.10      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ (k2_zfmisc_1 @ X52 @ X54) @ (k2_zfmisc_1 @ X53 @ X55))
% 1.91/2.10           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X52 @ X53) @ X54) @ 
% 1.91/2.10              (k2_zfmisc_1 @ X52 @ (k4_xboole_0 @ X54 @ X55))))),
% 1.91/2.10      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.91/2.10  thf('70', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_C @ X0))
% 1.91/2.10           = (k2_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ 
% 1.91/2.10              (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ X1 @ X0))))),
% 1.91/2.10      inference('sup+', [status(thm)], ['68', '69'])).
% 1.91/2.10  thf('71', plain,
% 1.91/2.10      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['16'])).
% 1.91/2.10  thf('72', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.10         ((k2_zfmisc_1 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 1.91/2.10           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.91/2.10              (k2_zfmisc_1 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 1.91/2.10      inference('demod', [status(thm)], ['35', '36', '39'])).
% 1.91/2.10  thf('73', plain,
% 1.91/2.10      (![X0 : $i, X1 : $i]:
% 1.91/2.10         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_C @ X0))
% 1.91/2.10           = (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ X1 @ X0)))),
% 1.91/2.10      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.91/2.10  thf('74', plain,
% 1.91/2.10      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))),
% 1.91/2.10      inference('demod', [status(thm)], ['3', '73'])).
% 1.91/2.10  thf('75', plain,
% 1.91/2.10      (![X41 : $i, X42 : $i]:
% 1.91/2.10         (((X41) = (k1_xboole_0))
% 1.91/2.10          | ((X42) = (k1_xboole_0))
% 1.91/2.10          | ((k2_zfmisc_1 @ X42 @ X41) != (k1_xboole_0)))),
% 1.91/2.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.91/2.10  thf('76', plain,
% 1.91/2.10      ((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.10        | ((sk_A) = (k1_xboole_0))
% 1.91/2.10        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['74', '75'])).
% 1.91/2.10  thf('77', plain,
% 1.91/2.10      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 1.91/2.10        | ((sk_A) = (k1_xboole_0)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['76'])).
% 1.91/2.10  thf('78', plain,
% 1.91/2.10      (![X1 : $i, X2 : $i]:
% 1.91/2.10         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 1.91/2.10      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.91/2.10  thf('79', plain,
% 1.91/2.10      ((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.10        | ((sk_A) = (k1_xboole_0))
% 1.91/2.10        | (r1_tarski @ sk_B @ sk_D))),
% 1.91/2.10      inference('sup-', [status(thm)], ['77', '78'])).
% 1.91/2.10  thf('80', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['79'])).
% 1.91/2.10  thf('81', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 1.91/2.10      inference('simpl_trail', [status(thm)], ['49', '66'])).
% 1.91/2.10  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 1.91/2.10      inference('clc', [status(thm)], ['80', '81'])).
% 1.91/2.10  thf('83', plain,
% 1.91/2.10      (![X43 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X43) = (k1_xboole_0))),
% 1.91/2.10      inference('simplify', [status(thm)], ['16'])).
% 1.91/2.10  thf('84', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.91/2.10      inference('demod', [status(thm)], ['0', '82', '83'])).
% 1.91/2.10  thf('85', plain, ($false), inference('simplify', [status(thm)], ['84'])).
% 1.91/2.10  
% 1.91/2.10  % SZS output end Refutation
% 1.91/2.10  
% 1.91/2.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
