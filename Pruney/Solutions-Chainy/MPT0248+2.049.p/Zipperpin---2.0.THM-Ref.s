%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfHKF8cCTn

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:24 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 348 expanded)
%              Number of leaves         :   26 ( 105 expanded)
%              Depth                    :   26
%              Number of atoms          :  922 (3608 expanded)
%              Number of equality atoms :  165 ( 755 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X22: $i] :
      ( ( k3_xboole_0 @ X22 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('18',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X61
        = ( k1_tarski @ X60 ) )
      | ( X61 = k1_xboole_0 )
      | ~ ( r1_tarski @ X61 @ ( k1_tarski @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('24',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_B )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32','42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('54',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_xboole_0
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('59',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('61',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X61
        = ( k1_tarski @ X60 ) )
      | ( X61 = k1_xboole_0 )
      | ~ ( r1_tarski @ X61 @ ( k1_tarski @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('63',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_B @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X31: $i] :
      ( ( k5_xboole_0 @ X31 @ X31 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('65',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ X30 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_C
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( ( k5_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','69'])).

thf('71',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('75',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['71'])).

thf('76',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['73','79'])).

thf('81',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('84',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('87',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['81'])).

thf('88',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['83','85','89'])).

thf('91',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','90'])).

thf('92',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['80','91'])).

thf('93',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['71'])).

thf('94',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['72','94'])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['70','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('98',plain,
    ( ( sk_C
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('100',plain,
    ( ( sk_C = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('102',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','90'])).

thf('103',plain,
    ( ( sk_C != sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','104'])).

thf('106',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['0','105'])).

thf('107',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['82','90'])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfHKF8cCTn
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 634 iterations in 0.186s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(t43_zfmisc_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.64          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.64          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.64          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.64             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.64             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.64             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.46/0.64  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf(t2_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X22 : $i]: ((k3_xboole_0 @ X22 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf(t100_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X10 @ X11)
% 0.46/0.64           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf(commutativity_k5_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.64  thf(t5_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('7', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.64  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['5', '8'])).
% 0.46/0.64  thf(l32_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i]:
% 0.46/0.64         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf(t12_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.64  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('15', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t7_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf('17', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf(l3_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.46/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X60 : $i, X61 : $i]:
% 0.46/0.64         (((X61) = (k1_tarski @ X60))
% 0.46/0.64          | ((X61) = (k1_xboole_0))
% 0.46/0.64          | ~ (r1_tarski @ X61 @ (k1_tarski @ X60)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('20', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf(l98_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k5_xboole_0 @ A @ B ) =
% 0.46/0.64       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ X8 @ X9)
% 0.46/0.64           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.64         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.64            (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.64  thf('25', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf(t28_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('27', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.64         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['24', '27'])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      ((((k5_xboole_0 @ sk_B @ sk_B)
% 0.46/0.64          = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.46/0.64        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['19', '28'])).
% 0.46/0.64  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.64  thf('30', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X10 @ X11)
% 0.46/0.64           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ X8 @ X9)
% 0.46/0.64           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('38', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.46/0.64  thf(t36_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 0.46/0.64      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.64  thf('40', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.64      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X5 : $i, X7 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.64  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      ((((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.46/0.64        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['29', '32', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X5 : $i, X6 : $i]:
% 0.46/0.64         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.64        | ((sk_B) = (k1_xboole_0))
% 0.46/0.64        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0))
% 0.46/0.64        | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0))
% 0.46/0.64        | ((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X10 @ X11)
% 0.46/0.64           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.64          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.64        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X5 : $i, X7 : $i]:
% 0.46/0.64         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      ((((k1_xboole_0) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.64        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '55'])).
% 0.46/0.64  thf('57', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ X8 @ X9)
% 0.46/0.64           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (((k5_xboole_0 @ sk_B @ sk_C)
% 0.46/0.64         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 0.46/0.64      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      ((r1_tarski @ (k5_xboole_0 @ sk_B @ sk_C) @ (k1_tarski @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X60 : $i, X61 : $i]:
% 0.46/0.64         (((X61) = (k1_tarski @ X60))
% 0.46/0.64          | ((X61) = (k1_xboole_0))
% 0.46/0.64          | ~ (r1_tarski @ X61 @ (k1_tarski @ X60)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      ((((k5_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | ((k5_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf(t92_xboole_1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('64', plain, (![X31 : $i]: ((k5_xboole_0 @ X31 @ X31) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.64  thf(t91_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.64       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ X30)
% 0.46/0.64           = (k5_xboole_0 @ X28 @ (k5_xboole_0 @ X29 @ X30)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['64', '65'])).
% 0.46/0.64  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      ((((sk_C) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.64        | ((k5_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['63', '68'])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      ((((sk_C) = (k1_xboole_0))
% 0.46/0.64        | ((sk_B) = (k1_xboole_0))
% 0.46/0.64        | ((k5_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['56', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['71'])).
% 0.46/0.64  thf('73', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.64      inference('split', [status(esa)], ['71'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.46/0.64         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['76'])).
% 0.46/0.64  thf('78', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.46/0.64         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['77', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['73', '79'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.46/0.64      inference('split', [status(esa)], ['81'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('split', [status(esa)], ['81'])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('split', [status(esa)], ['84'])).
% 0.46/0.64  thf('86', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['76'])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['81'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      ((((sk_B) != (sk_B)))
% 0.46/0.64         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['86', '87'])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['88'])).
% 0.46/0.64  thf('90', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['83', '85', '89'])).
% 0.46/0.64  thf('91', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['82', '90'])).
% 0.46/0.64  thf('92', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['80', '91'])).
% 0.46/0.64  thf('93', plain,
% 0.46/0.64      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('split', [status(esa)], ['71'])).
% 0.46/0.64  thf('94', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.46/0.64  thf('95', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['72', '94'])).
% 0.46/0.64  thf('96', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0))
% 0.46/0.64        | ((k5_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['70', '95'])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      ((((sk_C) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 0.46/0.64        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['96', '97'])).
% 0.46/0.64  thf('99', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.64  thf('100', plain, ((((sk_C) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['98', '99'])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('102', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['82', '90'])).
% 0.46/0.64  thf('103', plain, ((((sk_C) != (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.64  thf('104', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.64      inference('clc', [status(thm)], ['100', '103'])).
% 0.46/0.64  thf('105', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['14', '104'])).
% 0.46/0.64  thf('106', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '105'])).
% 0.46/0.64  thf('107', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['82', '90'])).
% 0.46/0.64  thf('108', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.52/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
