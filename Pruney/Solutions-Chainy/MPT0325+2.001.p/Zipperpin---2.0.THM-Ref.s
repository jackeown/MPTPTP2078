%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tP7mEDE0jr

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:40 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 249 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :   27
%              Number of atoms          :  945 (2233 expanded)
%              Number of equality atoms :  111 ( 240 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['5','6'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('8',plain,(
    ! [X63: $i,X65: $i,X66: $i] :
      ( ( k2_zfmisc_1 @ X66 @ ( k2_xboole_0 @ X63 @ X65 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X66 @ X63 ) @ ( k2_zfmisc_1 @ X66 @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X67 @ X69 ) @ ( k3_xboole_0 @ X68 @ X70 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X67 @ X68 ) @ ( k2_zfmisc_1 @ X69 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('15',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X63 @ X65 ) @ X64 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X63 @ X64 ) @ ( k2_zfmisc_1 @ X65 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['22','27','28'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('30',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( X60 = k1_xboole_0 )
      | ( r1_tarski @ X61 @ X62 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X60 @ X61 ) @ ( k2_zfmisc_1 @ X60 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('36',plain,
    ( ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) @ sk_B_1 )
      = ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('39',plain,
    ( ( sk_B_1
      = ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('52',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('53',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( X60 = k1_xboole_0 )
      | ( r1_tarski @ X61 @ X62 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X61 @ X60 ) @ ( k2_zfmisc_1 @ X62 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
      | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_A ) @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['5','6'])).

thf('57',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_A ) @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('60',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('64',plain,
    ( ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_A )
      = ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('67',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('69',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('70',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k2_zfmisc_1 @ X58 @ X59 )
        = k1_xboole_0 )
      | ( X59 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('71',plain,(
    ! [X58: $i] :
      ( ( k2_zfmisc_1 @ X58 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','71'])).

thf('73',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['49'])).

thf('83',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['49'])).

thf('85',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['50','85'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['48','86'])).

thf('88',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k2_zfmisc_1 @ X58 @ X59 )
        = k1_xboole_0 )
      | ( X58 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('89',plain,(
    ! [X59: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X59 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','87','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tP7mEDE0jr
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 500 iterations in 0.219s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.67  thf(t138_zfmisc_1, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.46/0.68       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.68         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.46/0.68          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.68            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.46/0.68  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.68  thf('1', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.46/0.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.68  thf(t100_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X13 @ X14)
% 0.46/0.68           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.68  thf(l32_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.68  thf('4', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i]:
% 0.46/0.68         ((r1_tarski @ X10 @ X11)
% 0.46/0.68          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k5_xboole_0 @ X0 @ X0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.68  thf(t92_xboole_1, axiom,
% 0.46/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.68  thf('6', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.68  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.68      inference('simplify_reflect+', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf(t120_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.46/0.68         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.46/0.68       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.68         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X63 : $i, X65 : $i, X66 : $i]:
% 0.46/0.68         ((k2_zfmisc_1 @ X66 @ (k2_xboole_0 @ X63 @ X65))
% 0.46/0.68           = (k2_xboole_0 @ (k2_zfmisc_1 @ X66 @ X63) @ 
% 0.46/0.68              (k2_zfmisc_1 @ X66 @ X65)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.46/0.68        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t28_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.46/0.68         (k2_zfmisc_1 @ sk_C_1 @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ 
% 0.46/0.68         (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.68  thf(t123_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.46/0.68       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 0.46/0.68         ((k2_zfmisc_1 @ (k3_xboole_0 @ X67 @ X69) @ (k3_xboole_0 @ X68 @ X70))
% 0.46/0.68           = (k3_xboole_0 @ (k2_zfmisc_1 @ X67 @ X68) @ 
% 0.46/0.68              (k2_zfmisc_1 @ X69 @ X70)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.46/0.68         (k3_xboole_0 @ sk_D @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.46/0.68         ((k2_zfmisc_1 @ (k2_xboole_0 @ X63 @ X65) @ X64)
% 0.46/0.68           = (k2_xboole_0 @ (k2_zfmisc_1 @ X63 @ X64) @ 
% 0.46/0.68              (k2_zfmisc_1 @ X65 @ X64)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k2_zfmisc_1 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ X0) @ 
% 0.46/0.68           (k3_xboole_0 @ sk_D @ sk_B_1))
% 0.46/0.68           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.46/0.68              (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B_1))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (((k2_zfmisc_1 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_A) @ 
% 0.46/0.68         (k3_xboole_0 @ sk_D @ sk_B_1))
% 0.46/0.68         = (k2_zfmisc_1 @ sk_A @ 
% 0.46/0.68            (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_D @ sk_B_1))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['8', '17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf(t22_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X15 : $i, X16 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)) = (X15))),
% 0.46/0.68      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (((k2_zfmisc_1 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_A) @ 
% 0.46/0.68         (k3_xboole_0 @ sk_D @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['18', '21'])).
% 0.46/0.68  thf(commutativity_k2_tarski, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X26 : $i, X27 : $i]:
% 0.46/0.68         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.68  thf(l51_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X55 : $i, X56 : $i]:
% 0.46/0.68         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.46/0.68      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X55 : $i, X56 : $i]:
% 0.46/0.68         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 0.46/0.68      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B_1))
% 0.46/0.68         = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['22', '27', '28'])).
% 0.46/0.68  thf(t117_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.68          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.46/0.68            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.46/0.68          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.46/0.68         (((X60) = (k1_xboole_0))
% 0.46/0.68          | (r1_tarski @ X61 @ X62)
% 0.46/0.68          | ~ (r1_tarski @ (k2_zfmisc_1 @ X60 @ X61) @ 
% 0.46/0.68               (k2_zfmisc_1 @ X60 @ X62)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 0.46/0.68             (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.46/0.68          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_D @ sk_B_1))
% 0.46/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      ((((sk_A) = (k1_xboole_0))
% 0.46/0.68        | (r1_tarski @ sk_B_1 @ (k3_xboole_0 @ sk_D @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['7', '31'])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      ((((sk_A) = (k1_xboole_0))
% 0.46/0.68        | ((k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_D @ sk_B_1)) = (sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      ((((k2_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_B_1) @ sk_B_1)
% 0.46/0.68          = (k3_xboole_0 @ sk_D @ sk_B_1))
% 0.46/0.68        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.68  thf('37', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      ((((sk_B_1) = (k3_xboole_0 @ sk_D @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X13 @ X14)
% 0.46/0.68           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      ((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))
% 0.46/0.68        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['39', '42'])).
% 0.46/0.68  thf('44', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      ((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 0.46/0.68        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.68  thf('46', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i]:
% 0.46/0.68         ((r1_tarski @ X10 @ X11)
% 0.46/0.68          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.68        | ((sk_A) = (k1_xboole_0))
% 0.46/0.68        | (r1_tarski @ sk_B_1 @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.68  thf('48', plain, (((r1_tarski @ sk_B_1 @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['47'])).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B_1 @ sk_D))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      ((~ (r1_tarski @ sk_B_1 @ sk_D)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 0.46/0.68      inference('split', [status(esa)], ['49'])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (((k2_zfmisc_1 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_A) @ 
% 0.46/0.68         (k3_xboole_0 @ sk_D @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['18', '21'])).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.46/0.68         (k3_xboole_0 @ sk_D @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.68  thf('53', plain,
% 0.46/0.68      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.46/0.68         (((X60) = (k1_xboole_0))
% 0.46/0.68          | (r1_tarski @ X61 @ X62)
% 0.46/0.68          | ~ (r1_tarski @ (k2_zfmisc_1 @ X61 @ X60) @ 
% 0.46/0.68               (k2_zfmisc_1 @ X62 @ X60)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B_1)) @ 
% 0.46/0.68             (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.46/0.68          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_C_1 @ sk_A))
% 0.46/0.68          | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.46/0.68           (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.46/0.68        | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))
% 0.46/0.68        | (r1_tarski @ (k2_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_A) @ 
% 0.46/0.68           (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['51', '54'])).
% 0.46/0.68  thf('56', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.68      inference('simplify_reflect+', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      ((((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))
% 0.46/0.68        | (r1_tarski @ (k2_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_A) @ 
% 0.46/0.68           (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.68  thf('58', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      ((((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))
% 0.46/0.68        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.46/0.68  thf('61', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('62', plain,
% 0.46/0.68      ((((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0))
% 0.46/0.68        | ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)) = (sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      ((((k2_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_A)
% 0.46/0.68          = (k3_xboole_0 @ sk_C_1 @ sk_A))
% 0.46/0.68        | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['62', '63'])).
% 0.46/0.68  thf('65', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf('66', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      ((((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))
% 0.46/0.68        | ((k3_xboole_0 @ sk_D @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.46/0.68         (k3_xboole_0 @ sk_D @ sk_B_1)) = (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      ((((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ k1_xboole_0)
% 0.46/0.68          = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.46/0.68        | ((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['67', '68'])).
% 0.46/0.68  thf(t113_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.68  thf('70', plain,
% 0.46/0.68      (![X58 : $i, X59 : $i]:
% 0.46/0.68         (((k2_zfmisc_1 @ X58 @ X59) = (k1_xboole_0))
% 0.46/0.68          | ((X59) != (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.68  thf('71', plain,
% 0.46/0.68      (![X58 : $i]: ((k2_zfmisc_1 @ X58 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.68      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.68  thf('72', plain,
% 0.46/0.68      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.46/0.68        | ((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['69', '71'])).
% 0.46/0.68  thf('73', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('74', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.46/0.68  thf('75', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('76', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['74', '75'])).
% 0.46/0.68  thf('77', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.46/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.68  thf('78', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.68  thf('79', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i]:
% 0.46/0.68         ((r1_tarski @ X10 @ X11)
% 0.46/0.68          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.68  thf('80', plain,
% 0.46/0.68      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_C_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.68  thf('81', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.46/0.68      inference('simplify', [status(thm)], ['80'])).
% 0.46/0.68  thf('82', plain,
% 0.46/0.68      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.46/0.68      inference('split', [status(esa)], ['49'])).
% 0.46/0.68  thf('83', plain, (((r1_tarski @ sk_A @ sk_C_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.68  thf('84', plain,
% 0.46/0.68      (~ ((r1_tarski @ sk_B_1 @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C_1))),
% 0.46/0.68      inference('split', [status(esa)], ['49'])).
% 0.46/0.68  thf('85', plain, (~ ((r1_tarski @ sk_B_1 @ sk_D))),
% 0.46/0.68      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.46/0.68  thf('86', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['50', '85'])).
% 0.46/0.68  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('clc', [status(thm)], ['48', '86'])).
% 0.46/0.68  thf('88', plain,
% 0.46/0.68      (![X58 : $i, X59 : $i]:
% 0.46/0.68         (((k2_zfmisc_1 @ X58 @ X59) = (k1_xboole_0))
% 0.46/0.68          | ((X58) != (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.68  thf('89', plain,
% 0.46/0.68      (![X59 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X59) = (k1_xboole_0))),
% 0.46/0.68      inference('simplify', [status(thm)], ['88'])).
% 0.46/0.68  thf('90', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['0', '87', '89'])).
% 0.46/0.68  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
