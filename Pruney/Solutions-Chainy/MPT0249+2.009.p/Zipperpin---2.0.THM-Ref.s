%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NMeULDKutY

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:39 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 280 expanded)
%              Number of leaves         :   29 (  98 expanded)
%              Depth                    :   17
%              Number of atoms          :  712 (2062 expanded)
%              Number of equality atoms :  104 ( 322 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49
        = ( k1_tarski @ X48 ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( r1_tarski @ X49 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('10',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49
        = ( k1_tarski @ X48 ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( r1_tarski @ X49 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('19',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k1_tarski @ X50 ) )
      | ( X49 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('22',plain,(
    ! [X50: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X50 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = sk_B )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference(demod,[status(thm)],['19','31'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( sk_C
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('53',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(t105_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ( ( k4_xboole_0 @ B @ A )
          = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X12 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t105_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( r2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( ( k5_xboole_0 @ X0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( r2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( r2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( r2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','66'])).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('72',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference(demod,[status(thm)],['40','49','72'])).

thf('74',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('77',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('79',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('81',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NMeULDKutY
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 520 iterations in 0.157s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.61  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(t44_zfmisc_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.41/0.61          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.41/0.61          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.41/0.61             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.41/0.61             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.41/0.61  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t7_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.41/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.61  thf('3', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.41/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf(l3_zfmisc_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.41/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X48 : $i, X49 : $i]:
% 0.41/0.61         (((X49) = (k1_tarski @ X48))
% 0.41/0.61          | ((X49) = (k1_xboole_0))
% 0.41/0.61          | ~ (r1_tarski @ X49 @ (k1_tarski @ X48)))),
% 0.41/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.41/0.61  thf('5', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.61  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('7', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.41/0.61  thf('8', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['0', '7'])).
% 0.41/0.61  thf(l98_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( k5_xboole_0 @ A @ B ) =
% 0.41/0.61       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         ((k5_xboole_0 @ X7 @ X8)
% 0.41/0.61           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.41/0.61      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (((k5_xboole_0 @ sk_B @ sk_C)
% 0.41/0.61         = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf(t17_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 0.41/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.41/0.61  thf('12', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X48 : $i, X49 : $i]:
% 0.41/0.61         (((X49) = (k1_tarski @ X48))
% 0.41/0.61          | ((X49) = (k1_xboole_0))
% 0.41/0.61          | ~ (r1_tarski @ X49 @ (k1_tarski @ X48)))),
% 0.41/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X0 @ sk_B)
% 0.41/0.61          | ((X0) = (k1_xboole_0))
% 0.41/0.61          | ((X0) = (k1_tarski @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.61  thf('15', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (((k3_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.41/0.61          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '16'])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (((k5_xboole_0 @ sk_B @ sk_C)
% 0.41/0.61         = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      ((((k5_xboole_0 @ sk_B @ sk_C) = (k4_xboole_0 @ sk_B @ k1_xboole_0))
% 0.41/0.61        | ((k3_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.41/0.61  thf('20', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X49 : $i, X50 : $i]:
% 0.41/0.61         ((r1_tarski @ X49 @ (k1_tarski @ X50)) | ((X49) != (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X50 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X50))),
% 0.41/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.41/0.61  thf(t28_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X15 : $i, X16 : $i]:
% 0.41/0.61         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf('25', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.41/0.61      inference('sup+', [status(thm)], ['20', '24'])).
% 0.41/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.61  thf('27', plain, (((k3_xboole_0 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.61      inference('demod', [status(thm)], ['25', '26'])).
% 0.41/0.61  thf(t100_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X9 @ X10)
% 0.41/0.61           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.41/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.41/0.61  thf(t5_boole, axiom,
% 0.41/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.61  thf('30', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.61  thf('31', plain, (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      ((((k5_xboole_0 @ sk_B @ sk_C) = (sk_B))
% 0.41/0.62        | ((k3_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.41/0.62      inference('demod', [status(thm)], ['19', '31'])).
% 0.41/0.62  thf(t92_xboole_1, axiom,
% 0.41/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.62  thf('33', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.62  thf(t91_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.41/0.62           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['33', '34'])).
% 0.41/0.62  thf(commutativity_k5_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.41/0.62  thf('37', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.62  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['36', '37'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['35', '38'])).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      ((((sk_C) = (k5_xboole_0 @ sk_B @ sk_B))
% 0.41/0.62        | ((k3_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['32', '39'])).
% 0.41/0.62  thf('41', plain,
% 0.41/0.62      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 0.41/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.41/0.62  thf('45', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.41/0.62      inference('sup+', [status(thm)], ['43', '44'])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.62  thf('47', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X9 @ X10)
% 0.41/0.62           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.62  thf(d8_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.41/0.62       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (![X4 : $i, X6 : $i]:
% 0.41/0.62         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.41/0.62      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 0.41/0.62          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.62  thf(t69_enumset1, axiom,
% 0.41/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.41/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.62  thf(l51_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      (![X51 : $i, X52 : $i]:
% 0.41/0.62         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.41/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.62  thf('55', plain,
% 0.41/0.62      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['53', '54'])).
% 0.41/0.62  thf('56', plain,
% 0.41/0.62      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['53', '54'])).
% 0.41/0.62  thf('57', plain,
% 0.41/0.62      (![X7 : $i, X8 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ X7 @ X8)
% 0.41/0.62           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.41/0.62      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.41/0.62  thf(t105_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.41/0.62          ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i]:
% 0.41/0.62         (~ (r2_xboole_0 @ X11 @ X12)
% 0.41/0.62          | ((k4_xboole_0 @ X12 @ X11) != (k1_xboole_0)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t105_xboole_1])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (((k5_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.41/0.62          | ~ (r2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.62  thf('60', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ 
% 0.41/0.62             (k3_tarski @ (k1_tarski @ X0)))
% 0.41/0.62          | ((k5_xboole_0 @ X0 @ X0) != (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['56', '59'])).
% 0.41/0.62  thf('61', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.62  thf('62', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ 
% 0.41/0.62             (k3_tarski @ (k1_tarski @ X0)))
% 0.41/0.62          | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['60', '61'])).
% 0.41/0.62  thf('63', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ~ (r2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ 
% 0.41/0.62            (k3_tarski @ (k1_tarski @ X0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['62'])).
% 0.41/0.62  thf('64', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ~ (r2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['55', '63'])).
% 0.41/0.62  thf('65', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.62  thf('66', plain,
% 0.41/0.62      (![X0 : $i]: ~ (r2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['64', '65'])).
% 0.41/0.62  thf('67', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['52', '66'])).
% 0.41/0.62  thf('68', plain,
% 0.41/0.62      (![X7 : $i, X8 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ X7 @ X8)
% 0.41/0.62           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.41/0.62      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.41/0.62  thf('69', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ X0 @ X0)
% 0.41/0.62           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['67', '68'])).
% 0.41/0.62  thf('70', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.62  thf('71', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.62  thf('72', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.41/0.62  thf('73', plain,
% 0.41/0.62      ((((sk_C) = (k1_xboole_0)) | ((k3_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.41/0.62      inference('demod', [status(thm)], ['40', '49', '72'])).
% 0.41/0.62  thf('74', plain, (((sk_C) != (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('75', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.41/0.62  thf('76', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.41/0.62  thf('77', plain, (((k5_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['10', '75', '76'])).
% 0.41/0.62  thf('78', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['35', '38'])).
% 0.41/0.62  thf('79', plain, (((sk_C) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['77', '78'])).
% 0.41/0.62  thf('80', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.62  thf('81', plain, (((sk_C) = (sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['79', '80'])).
% 0.41/0.62  thf('82', plain, (((sk_B) != (sk_C))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('83', plain, ($false),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
