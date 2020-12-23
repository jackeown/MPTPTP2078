%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J4hEdcPrJy

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:42 EST 2020

% Result     : Theorem 5.03s
% Output     : Refutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 194 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   26
%              Number of atoms          :  817 (1574 expanded)
%              Number of equality atoms :   88 ( 159 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('20',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('21',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_zfmisc_1 @ X35 @ X36 )
        = k1_xboole_0 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('25',plain,(
    ! [X35: $i] :
      ( ( k2_zfmisc_1 @ X35 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 )
      | ( r1_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','38'])).

thf('40',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','39'])).

thf('41',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X35 @ X34 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( ( k4_xboole_0 @ X14 @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_zfmisc_1 @ X35 @ X36 )
        = k1_xboole_0 )
      | ( X35 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X36: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X36 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X2 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X2 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ sk_C_2 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X1 @ sk_C_2 ) ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','64'])).

thf('66',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','65'])).

thf('67',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X35 @ X34 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( ( k4_xboole_0 @ X14 @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_A @ sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['47'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X35: $i] :
      ( ( k2_zfmisc_1 @ X35 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['47'])).

thf('81',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['48','81'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['46','82'])).

thf('84',plain,(
    ! [X36: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X36 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('85',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','83','84'])).

thf('86',plain,(
    $false ),
    inference(simplify,[status(thm)],['85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J4hEdcPrJy
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.03/5.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.03/5.28  % Solved by: fo/fo7.sh
% 5.03/5.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.03/5.28  % done 14867 iterations in 4.828s
% 5.03/5.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.03/5.28  % SZS output start Refutation
% 5.03/5.28  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.03/5.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.03/5.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.03/5.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.03/5.28  thf(sk_B_type, type, sk_B: $i).
% 5.03/5.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.03/5.28  thf(sk_C_2_type, type, sk_C_2: $i).
% 5.03/5.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.03/5.28  thf(sk_A_type, type, sk_A: $i).
% 5.03/5.28  thf(sk_D_type, type, sk_D: $i).
% 5.03/5.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.03/5.28  thf(t138_zfmisc_1, conjecture,
% 5.03/5.28    (![A:$i,B:$i,C:$i,D:$i]:
% 5.03/5.28     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 5.03/5.28       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 5.03/5.28         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 5.03/5.28  thf(zf_stmt_0, negated_conjecture,
% 5.03/5.28    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.03/5.28        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 5.03/5.28          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 5.03/5.28            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 5.03/5.28    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 5.03/5.28  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 5.03/5.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.28  thf(t1_boole, axiom,
% 5.03/5.28    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.03/5.28  thf('1', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 5.03/5.28      inference('cnf', [status(esa)], [t1_boole])).
% 5.03/5.28  thf(t7_xboole_1, axiom,
% 5.03/5.28    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.03/5.28  thf('2', plain,
% 5.03/5.28      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 5.03/5.28      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.03/5.28  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.03/5.28      inference('sup+', [status(thm)], ['1', '2'])).
% 5.03/5.28  thf(t106_xboole_1, axiom,
% 5.03/5.28    (![A:$i,B:$i,C:$i]:
% 5.03/5.28     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 5.03/5.28       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 5.03/5.28  thf('4', plain,
% 5.03/5.28      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.03/5.28         ((r1_tarski @ X17 @ X18)
% 5.03/5.28          | ~ (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X19)))),
% 5.03/5.28      inference('cnf', [status(esa)], [t106_xboole_1])).
% 5.03/5.28  thf('5', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 5.03/5.28      inference('sup-', [status(thm)], ['3', '4'])).
% 5.03/5.28  thf(t28_xboole_1, axiom,
% 5.03/5.28    (![A:$i,B:$i]:
% 5.03/5.28     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.03/5.28  thf('6', plain,
% 5.03/5.28      (![X21 : $i, X22 : $i]:
% 5.03/5.28         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 5.03/5.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.03/5.28  thf('7', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 5.03/5.28           = (k4_xboole_0 @ X0 @ X1))),
% 5.03/5.28      inference('sup-', [status(thm)], ['5', '6'])).
% 5.03/5.28  thf(commutativity_k3_xboole_0, axiom,
% 5.03/5.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.03/5.28  thf('8', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.03/5.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.03/5.28  thf('9', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 5.03/5.28           = (k4_xboole_0 @ X0 @ X1))),
% 5.03/5.28      inference('demod', [status(thm)], ['7', '8'])).
% 5.03/5.28  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.03/5.28      inference('sup+', [status(thm)], ['1', '2'])).
% 5.03/5.28  thf('11', plain,
% 5.03/5.28      (![X21 : $i, X22 : $i]:
% 5.03/5.28         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 5.03/5.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.03/5.28  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 5.03/5.28      inference('sup-', [status(thm)], ['10', '11'])).
% 5.03/5.28  thf('13', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.03/5.28      inference('sup+', [status(thm)], ['1', '2'])).
% 5.03/5.28  thf('14', plain,
% 5.03/5.28      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.03/5.28         ((r1_xboole_0 @ X17 @ X19)
% 5.03/5.28          | ~ (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X19)))),
% 5.03/5.28      inference('cnf', [status(esa)], [t106_xboole_1])).
% 5.03/5.28  thf('15', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 5.03/5.28      inference('sup-', [status(thm)], ['13', '14'])).
% 5.03/5.28  thf(d7_xboole_0, axiom,
% 5.03/5.28    (![A:$i,B:$i]:
% 5.03/5.28     ( ( r1_xboole_0 @ A @ B ) <=>
% 5.03/5.28       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 5.03/5.28  thf('16', plain,
% 5.03/5.28      (![X2 : $i, X3 : $i]:
% 5.03/5.28         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.03/5.28      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.03/5.28  thf('17', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 5.03/5.28      inference('sup-', [status(thm)], ['15', '16'])).
% 5.03/5.28  thf('18', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.03/5.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.03/5.28  thf('19', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 5.03/5.28      inference('demod', [status(thm)], ['17', '18'])).
% 5.03/5.28  thf(t123_zfmisc_1, axiom,
% 5.03/5.28    (![A:$i,B:$i,C:$i,D:$i]:
% 5.03/5.28     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 5.03/5.28       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 5.03/5.28  thf('20', plain,
% 5.03/5.28      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 5.03/5.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 5.03/5.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 5.03/5.28              (k2_zfmisc_1 @ X49 @ X50)))),
% 5.03/5.28      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 5.03/5.28  thf('21', plain,
% 5.03/5.28      (![X2 : $i, X4 : $i]:
% 5.03/5.28         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.03/5.28      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.03/5.28  thf('22', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 5.03/5.28            != (k1_xboole_0))
% 5.03/5.28          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 5.03/5.28      inference('sup-', [status(thm)], ['20', '21'])).
% 5.03/5.28  thf('23', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ k1_xboole_0)
% 5.03/5.28            != (k1_xboole_0))
% 5.03/5.28          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X0) @ 
% 5.03/5.28             (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 5.03/5.28      inference('sup-', [status(thm)], ['19', '22'])).
% 5.03/5.28  thf(t113_zfmisc_1, axiom,
% 5.03/5.28    (![A:$i,B:$i]:
% 5.03/5.28     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.03/5.28       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.03/5.28  thf('24', plain,
% 5.03/5.28      (![X35 : $i, X36 : $i]:
% 5.03/5.28         (((k2_zfmisc_1 @ X35 @ X36) = (k1_xboole_0))
% 5.03/5.28          | ((X36) != (k1_xboole_0)))),
% 5.03/5.28      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.03/5.28  thf('25', plain,
% 5.03/5.28      (![X35 : $i]: ((k2_zfmisc_1 @ X35 @ k1_xboole_0) = (k1_xboole_0))),
% 5.03/5.28      inference('simplify', [status(thm)], ['24'])).
% 5.03/5.28  thf('26', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         (((k1_xboole_0) != (k1_xboole_0))
% 5.03/5.28          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X0) @ 
% 5.03/5.28             (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 5.03/5.28      inference('demod', [status(thm)], ['23', '25'])).
% 5.03/5.28  thf('27', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X0) @ 
% 5.03/5.28          (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.03/5.28      inference('simplify', [status(thm)], ['26'])).
% 5.03/5.28  thf('28', plain,
% 5.03/5.28      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 5.03/5.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.28  thf(t63_xboole_1, axiom,
% 5.03/5.28    (![A:$i,B:$i,C:$i]:
% 5.03/5.28     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 5.03/5.28       ( r1_xboole_0 @ A @ C ) ))).
% 5.03/5.28  thf('29', plain,
% 5.03/5.28      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.03/5.28         (~ (r1_tarski @ X26 @ X27)
% 5.03/5.28          | ~ (r1_xboole_0 @ X27 @ X28)
% 5.03/5.28          | (r1_xboole_0 @ X26 @ X28))),
% 5.03/5.28      inference('cnf', [status(esa)], [t63_xboole_1])).
% 5.03/5.28  thf('30', plain,
% 5.03/5.28      (![X0 : $i]:
% 5.03/5.28         ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.03/5.28          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ X0))),
% 5.03/5.28      inference('sup-', [status(thm)], ['28', '29'])).
% 5.03/5.28  thf('31', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 5.03/5.28          (k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_D)))),
% 5.03/5.28      inference('sup-', [status(thm)], ['27', '30'])).
% 5.03/5.28  thf('32', plain,
% 5.03/5.28      (![X2 : $i, X3 : $i]:
% 5.03/5.28         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.03/5.28      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.03/5.28  thf('33', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 5.03/5.28           (k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_D))) = (k1_xboole_0))),
% 5.03/5.28      inference('sup-', [status(thm)], ['31', '32'])).
% 5.03/5.28  thf('34', plain,
% 5.03/5.28      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 5.03/5.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 5.03/5.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 5.03/5.28              (k2_zfmisc_1 @ X49 @ X50)))),
% 5.03/5.28      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 5.03/5.28  thf('35', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.03/5.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.03/5.28  thf('36', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1))
% 5.03/5.28           = (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 5.03/5.28      inference('sup+', [status(thm)], ['34', '35'])).
% 5.03/5.28  thf('37', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.03/5.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.03/5.28  thf('38', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ 
% 5.03/5.28           (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_D))) = (k1_xboole_0))),
% 5.03/5.28      inference('demod', [status(thm)], ['33', '36', '37'])).
% 5.03/5.28  thf('39', plain,
% 5.03/5.28      (![X0 : $i]:
% 5.03/5.28         ((k2_zfmisc_1 @ sk_A @ 
% 5.03/5.28           (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_D))) = (k1_xboole_0))),
% 5.03/5.28      inference('sup+', [status(thm)], ['12', '38'])).
% 5.03/5.28  thf('40', plain,
% 5.03/5.28      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))),
% 5.03/5.28      inference('sup+', [status(thm)], ['9', '39'])).
% 5.03/5.28  thf('41', plain,
% 5.03/5.28      (![X34 : $i, X35 : $i]:
% 5.03/5.28         (((X34) = (k1_xboole_0))
% 5.03/5.28          | ((X35) = (k1_xboole_0))
% 5.03/5.28          | ((k2_zfmisc_1 @ X35 @ X34) != (k1_xboole_0)))),
% 5.03/5.28      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.03/5.28  thf('42', plain,
% 5.03/5.28      ((((k1_xboole_0) != (k1_xboole_0))
% 5.03/5.28        | ((sk_A) = (k1_xboole_0))
% 5.03/5.28        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 5.03/5.28      inference('sup-', [status(thm)], ['40', '41'])).
% 5.03/5.28  thf('43', plain,
% 5.03/5.28      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 5.03/5.28        | ((sk_A) = (k1_xboole_0)))),
% 5.03/5.28      inference('simplify', [status(thm)], ['42'])).
% 5.03/5.28  thf(l32_xboole_1, axiom,
% 5.03/5.28    (![A:$i,B:$i]:
% 5.03/5.28     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.03/5.28  thf('44', plain,
% 5.03/5.28      (![X14 : $i, X15 : $i]:
% 5.03/5.28         ((r1_tarski @ X14 @ X15)
% 5.03/5.28          | ((k4_xboole_0 @ X14 @ X15) != (k1_xboole_0)))),
% 5.03/5.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 5.03/5.28  thf('45', plain,
% 5.03/5.28      ((((k1_xboole_0) != (k1_xboole_0))
% 5.03/5.28        | ((sk_A) = (k1_xboole_0))
% 5.03/5.28        | (r1_tarski @ sk_B @ sk_D))),
% 5.03/5.28      inference('sup-', [status(thm)], ['43', '44'])).
% 5.03/5.28  thf('46', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 5.03/5.28      inference('simplify', [status(thm)], ['45'])).
% 5.03/5.28  thf('47', plain,
% 5.03/5.28      ((~ (r1_tarski @ sk_A @ sk_C_2) | ~ (r1_tarski @ sk_B @ sk_D))),
% 5.03/5.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.28  thf('48', plain,
% 5.03/5.28      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 5.03/5.28      inference('split', [status(esa)], ['47'])).
% 5.03/5.28  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 5.03/5.28      inference('sup-', [status(thm)], ['10', '11'])).
% 5.03/5.28  thf('50', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 5.03/5.28           = (k4_xboole_0 @ X0 @ X1))),
% 5.03/5.28      inference('demod', [status(thm)], ['7', '8'])).
% 5.03/5.28  thf('51', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 5.03/5.28      inference('demod', [status(thm)], ['17', '18'])).
% 5.03/5.28  thf('52', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 5.03/5.28            != (k1_xboole_0))
% 5.03/5.28          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 5.03/5.28      inference('sup-', [status(thm)], ['20', '21'])).
% 5.03/5.28  thf('53', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         (((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 5.03/5.28            != (k1_xboole_0))
% 5.03/5.28          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 5.03/5.28             (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X2) @ X0)))),
% 5.03/5.28      inference('sup-', [status(thm)], ['51', '52'])).
% 5.03/5.28  thf('54', plain,
% 5.03/5.28      (![X35 : $i, X36 : $i]:
% 5.03/5.28         (((k2_zfmisc_1 @ X35 @ X36) = (k1_xboole_0))
% 5.03/5.28          | ((X35) != (k1_xboole_0)))),
% 5.03/5.28      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.03/5.28  thf('55', plain,
% 5.03/5.28      (![X36 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X36) = (k1_xboole_0))),
% 5.03/5.28      inference('simplify', [status(thm)], ['54'])).
% 5.03/5.28  thf('56', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         (((k1_xboole_0) != (k1_xboole_0))
% 5.03/5.28          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 5.03/5.28             (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X2) @ X0)))),
% 5.03/5.28      inference('demod', [status(thm)], ['53', '55'])).
% 5.03/5.28  thf('57', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 5.03/5.28          (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X2) @ X0))),
% 5.03/5.28      inference('simplify', [status(thm)], ['56'])).
% 5.03/5.28  thf('58', plain,
% 5.03/5.28      (![X0 : $i]:
% 5.03/5.28         ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 5.03/5.28          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ X0))),
% 5.03/5.28      inference('sup-', [status(thm)], ['28', '29'])).
% 5.03/5.28  thf('59', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 5.03/5.28          (k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ sk_C_2) @ X0))),
% 5.03/5.28      inference('sup-', [status(thm)], ['57', '58'])).
% 5.03/5.28  thf('60', plain,
% 5.03/5.28      (![X2 : $i, X3 : $i]:
% 5.03/5.28         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.03/5.28      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.03/5.28  thf('61', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 5.03/5.28           (k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ sk_C_2) @ X0)) = (k1_xboole_0))),
% 5.03/5.28      inference('sup-', [status(thm)], ['59', '60'])).
% 5.03/5.28  thf('62', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.03/5.28         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1))
% 5.03/5.28           = (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 5.03/5.28      inference('sup+', [status(thm)], ['34', '35'])).
% 5.03/5.28  thf('63', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.03/5.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.03/5.28  thf('64', plain,
% 5.03/5.28      (![X0 : $i, X1 : $i]:
% 5.03/5.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X1 @ sk_C_2)) @ 
% 5.03/5.28           (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 5.03/5.28      inference('demod', [status(thm)], ['61', '62', '63'])).
% 5.03/5.28  thf('65', plain,
% 5.03/5.28      (![X0 : $i]:
% 5.03/5.28         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ 
% 5.03/5.28           (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 5.03/5.28      inference('sup+', [status(thm)], ['50', '64'])).
% 5.03/5.28  thf('66', plain,
% 5.03/5.28      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_B) = (k1_xboole_0))),
% 5.03/5.28      inference('sup+', [status(thm)], ['49', '65'])).
% 5.03/5.28  thf('67', plain,
% 5.03/5.28      (![X34 : $i, X35 : $i]:
% 5.03/5.28         (((X34) = (k1_xboole_0))
% 5.03/5.28          | ((X35) = (k1_xboole_0))
% 5.03/5.28          | ((k2_zfmisc_1 @ X35 @ X34) != (k1_xboole_0)))),
% 5.03/5.28      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.03/5.28  thf('68', plain,
% 5.03/5.28      ((((k1_xboole_0) != (k1_xboole_0))
% 5.03/5.28        | ((k4_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))
% 5.03/5.28        | ((sk_B) = (k1_xboole_0)))),
% 5.03/5.28      inference('sup-', [status(thm)], ['66', '67'])).
% 5.03/5.28  thf('69', plain,
% 5.03/5.28      ((((sk_B) = (k1_xboole_0))
% 5.03/5.28        | ((k4_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0)))),
% 5.03/5.28      inference('simplify', [status(thm)], ['68'])).
% 5.03/5.28  thf('70', plain,
% 5.03/5.28      (![X14 : $i, X15 : $i]:
% 5.03/5.28         ((r1_tarski @ X14 @ X15)
% 5.03/5.28          | ((k4_xboole_0 @ X14 @ X15) != (k1_xboole_0)))),
% 5.03/5.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 5.03/5.28  thf('71', plain,
% 5.03/5.28      ((((k1_xboole_0) != (k1_xboole_0))
% 5.03/5.28        | ((sk_B) = (k1_xboole_0))
% 5.03/5.28        | (r1_tarski @ sk_A @ sk_C_2))),
% 5.03/5.28      inference('sup-', [status(thm)], ['69', '70'])).
% 5.03/5.28  thf('72', plain, (((r1_tarski @ sk_A @ sk_C_2) | ((sk_B) = (k1_xboole_0)))),
% 5.03/5.28      inference('simplify', [status(thm)], ['71'])).
% 5.03/5.28  thf('73', plain,
% 5.03/5.28      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 5.03/5.28      inference('split', [status(esa)], ['47'])).
% 5.03/5.28  thf('74', plain,
% 5.03/5.28      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 5.03/5.28      inference('sup-', [status(thm)], ['72', '73'])).
% 5.03/5.28  thf('75', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 5.03/5.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.03/5.28  thf('76', plain,
% 5.03/5.28      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 5.03/5.28         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 5.03/5.28      inference('sup-', [status(thm)], ['74', '75'])).
% 5.03/5.28  thf('77', plain,
% 5.03/5.28      (![X35 : $i]: ((k2_zfmisc_1 @ X35 @ k1_xboole_0) = (k1_xboole_0))),
% 5.03/5.28      inference('simplify', [status(thm)], ['24'])).
% 5.03/5.28  thf('78', plain,
% 5.03/5.28      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 5.03/5.28      inference('demod', [status(thm)], ['76', '77'])).
% 5.03/5.28  thf('79', plain, (((r1_tarski @ sk_A @ sk_C_2))),
% 5.03/5.28      inference('simplify', [status(thm)], ['78'])).
% 5.03/5.28  thf('80', plain,
% 5.03/5.28      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C_2))),
% 5.03/5.28      inference('split', [status(esa)], ['47'])).
% 5.03/5.28  thf('81', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 5.03/5.28      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 5.03/5.28  thf('82', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 5.03/5.28      inference('simpl_trail', [status(thm)], ['48', '81'])).
% 5.03/5.28  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 5.03/5.28      inference('clc', [status(thm)], ['46', '82'])).
% 5.03/5.28  thf('84', plain,
% 5.03/5.28      (![X36 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X36) = (k1_xboole_0))),
% 5.03/5.28      inference('simplify', [status(thm)], ['54'])).
% 5.03/5.28  thf('85', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 5.03/5.28      inference('demod', [status(thm)], ['0', '83', '84'])).
% 5.03/5.28  thf('86', plain, ($false), inference('simplify', [status(thm)], ['85'])).
% 5.03/5.28  
% 5.03/5.28  % SZS output end Refutation
% 5.03/5.28  
% 5.15/5.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
