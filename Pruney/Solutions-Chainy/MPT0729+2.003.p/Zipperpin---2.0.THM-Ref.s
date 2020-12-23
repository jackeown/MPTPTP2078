%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yrnJv62heF

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:41 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 244 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  816 (1716 expanded)
%              Number of equality atoms :   63 ( 165 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('0',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X33: $i] :
      ( ( k1_ordinal1 @ X33 )
      = ( k2_xboole_0 @ X33 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X33: $i] :
      ( ( k1_ordinal1 @ X33 )
      = ( k2_xboole_0 @ X33 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k2_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25
        = ( k1_tarski @ X24 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X33: $i] :
      ( ( k1_ordinal1 @ X33 )
      = ( k2_xboole_0 @ X33 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
      | ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ ( k2_tarski @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('40',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( r1_tarski @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['42','47'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X3 = X2 )
      | ( ( k4_xboole_0 @ X3 @ X2 )
       != ( k4_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('50',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('52',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k2_tarski @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25
        = ( k1_tarski @ X24 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('61',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
      | ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ sk_B )
      | ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ sk_B )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('76',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('78',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( r1_tarski @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('80',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','80'])).

thf('82',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('84',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('86',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['81','86'])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['50','87'])).

thf('89',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yrnJv62heF
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.97/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.97/1.14  % Solved by: fo/fo7.sh
% 0.97/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.14  % done 2169 iterations in 0.680s
% 0.97/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.97/1.14  % SZS output start Refutation
% 0.97/1.14  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.97/1.14  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.97/1.14  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.97/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.97/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.97/1.14  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.97/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.14  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.97/1.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.97/1.14  thf(t12_ordinal1, conjecture,
% 0.97/1.14    (![A:$i,B:$i]:
% 0.97/1.14     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 0.97/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.14    (~( ![A:$i,B:$i]:
% 0.97/1.14        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 0.97/1.14    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 0.97/1.14  thf('0', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf(d1_ordinal1, axiom,
% 0.97/1.14    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.97/1.14  thf('1', plain,
% 0.97/1.14      (![X33 : $i]:
% 0.97/1.14         ((k1_ordinal1 @ X33) = (k2_xboole_0 @ X33 @ (k1_tarski @ X33)))),
% 0.97/1.14      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.97/1.14  thf(t7_xboole_1, axiom,
% 0.97/1.14    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.97/1.14  thf('2', plain,
% 0.97/1.14      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.97/1.14      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.97/1.14  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.97/1.14      inference('sup+', [status(thm)], ['1', '2'])).
% 0.97/1.14  thf('4', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.97/1.14      inference('sup+', [status(thm)], ['0', '3'])).
% 0.97/1.14  thf(t69_enumset1, axiom,
% 0.97/1.14    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.97/1.14  thf('5', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.97/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.14  thf('6', plain,
% 0.97/1.14      (![X33 : $i]:
% 0.97/1.14         ((k1_ordinal1 @ X33) = (k2_xboole_0 @ X33 @ (k1_tarski @ X33)))),
% 0.97/1.14      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.97/1.14  thf('7', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.97/1.14      inference('sup+', [status(thm)], ['5', '6'])).
% 0.97/1.14  thf(t43_xboole_1, axiom,
% 0.97/1.14    (![A:$i,B:$i,C:$i]:
% 0.97/1.14     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.97/1.14       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.97/1.14  thf('8', plain,
% 0.97/1.14      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.97/1.14         ((r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.97/1.14          | ~ (r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.97/1.14      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.97/1.14  thf('9', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 0.97/1.14          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_tarski @ X0 @ X0)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.97/1.14  thf('10', plain,
% 0.97/1.14      ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ (k2_tarski @ sk_A @ sk_A))),
% 0.97/1.14      inference('sup-', [status(thm)], ['4', '9'])).
% 0.97/1.14  thf('11', plain,
% 0.97/1.14      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.97/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.14  thf('12', plain,
% 0.97/1.14      ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_A))),
% 0.97/1.14      inference('demod', [status(thm)], ['10', '11'])).
% 0.97/1.14  thf(l3_zfmisc_1, axiom,
% 0.97/1.14    (![A:$i,B:$i]:
% 0.97/1.14     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.97/1.14       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.97/1.14  thf('13', plain,
% 0.97/1.14      (![X24 : $i, X25 : $i]:
% 0.97/1.14         (((X25) = (k1_tarski @ X24))
% 0.97/1.14          | ((X25) = (k1_xboole_0))
% 0.97/1.14          | ~ (r1_tarski @ X25 @ (k1_tarski @ X24)))),
% 0.97/1.14      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.97/1.14  thf('14', plain,
% 0.97/1.14      ((((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.97/1.14        | ((k4_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_A)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['12', '13'])).
% 0.97/1.14  thf(t36_xboole_1, axiom,
% 0.97/1.14    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.97/1.14  thf('15', plain,
% 0.97/1.14      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.97/1.14      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.97/1.14  thf('16', plain,
% 0.97/1.14      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 0.97/1.14        | ((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.97/1.14      inference('sup+', [status(thm)], ['14', '15'])).
% 0.97/1.14  thf('17', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('18', plain,
% 0.97/1.14      (![X33 : $i]:
% 0.97/1.14         ((k1_ordinal1 @ X33) = (k2_xboole_0 @ X33 @ (k1_tarski @ X33)))),
% 0.97/1.14      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.97/1.14  thf(commutativity_k2_tarski, axiom,
% 0.97/1.14    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.97/1.14  thf('19', plain,
% 0.97/1.14      (![X14 : $i, X15 : $i]:
% 0.97/1.14         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.97/1.14      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.97/1.14  thf(l51_zfmisc_1, axiom,
% 0.97/1.14    (![A:$i,B:$i]:
% 0.97/1.14     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.97/1.14  thf('20', plain,
% 0.97/1.14      (![X27 : $i, X28 : $i]:
% 0.97/1.14         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 0.97/1.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.97/1.14  thf('21', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.97/1.14      inference('sup+', [status(thm)], ['19', '20'])).
% 0.97/1.14  thf('22', plain,
% 0.97/1.14      (![X27 : $i, X28 : $i]:
% 0.97/1.14         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 0.97/1.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.97/1.14  thf('23', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.97/1.14      inference('sup+', [status(thm)], ['21', '22'])).
% 0.97/1.14  thf('24', plain,
% 0.97/1.14      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.97/1.14      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.97/1.14  thf('25', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.97/1.14      inference('sup+', [status(thm)], ['23', '24'])).
% 0.97/1.14  thf('26', plain,
% 0.97/1.14      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))),
% 0.97/1.14      inference('sup+', [status(thm)], ['18', '25'])).
% 0.97/1.14  thf('27', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_ordinal1 @ sk_A))),
% 0.97/1.14      inference('sup+', [status(thm)], ['17', '26'])).
% 0.97/1.14  thf(l27_zfmisc_1, axiom,
% 0.97/1.14    (![A:$i,B:$i]:
% 0.97/1.14     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.97/1.14  thf('28', plain,
% 0.97/1.14      (![X22 : $i, X23 : $i]:
% 0.97/1.14         ((r1_xboole_0 @ (k1_tarski @ X22) @ X23) | (r2_hidden @ X22 @ X23))),
% 0.97/1.14      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.97/1.14  thf('29', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.97/1.14      inference('sup+', [status(thm)], ['5', '6'])).
% 0.97/1.14  thf(t73_xboole_1, axiom,
% 0.97/1.14    (![A:$i,B:$i,C:$i]:
% 0.97/1.14     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.97/1.14       ( r1_tarski @ A @ B ) ))).
% 0.97/1.14  thf('30', plain,
% 0.97/1.14      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.97/1.14         ((r1_tarski @ X9 @ X10)
% 0.97/1.14          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.97/1.14          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.97/1.14      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.97/1.14  thf('31', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 0.97/1.14          | ~ (r1_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0))
% 0.97/1.14          | (r1_tarski @ X1 @ X0))),
% 0.97/1.14      inference('sup-', [status(thm)], ['29', '30'])).
% 0.97/1.14  thf('32', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         ((r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.97/1.14          | (r1_tarski @ (k1_tarski @ X1) @ X0)
% 0.97/1.14          | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_ordinal1 @ X0)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['28', '31'])).
% 0.97/1.14  thf('33', plain,
% 0.97/1.14      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.97/1.14        | (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_A)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['27', '32'])).
% 0.97/1.14  thf('34', plain,
% 0.97/1.14      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.97/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.14  thf('35', plain,
% 0.97/1.14      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.97/1.14        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.97/1.14      inference('demod', [status(thm)], ['33', '34'])).
% 0.97/1.14  thf('36', plain,
% 0.97/1.14      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.97/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.14  thf(t38_zfmisc_1, axiom,
% 0.97/1.14    (![A:$i,B:$i,C:$i]:
% 0.97/1.14     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.97/1.14       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.97/1.14  thf('37', plain,
% 0.97/1.14      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.97/1.14         ((r2_hidden @ X29 @ X30)
% 0.97/1.14          | ~ (r1_tarski @ (k2_tarski @ X29 @ X31) @ X30))),
% 0.97/1.14      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.97/1.14  thf('38', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.97/1.14      inference('sup-', [status(thm)], ['36', '37'])).
% 0.97/1.14  thf('39', plain,
% 0.97/1.14      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.97/1.14      inference('sup-', [status(thm)], ['35', '38'])).
% 0.97/1.14  thf(t7_ordinal1, axiom,
% 0.97/1.14    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.97/1.14  thf('40', plain,
% 0.97/1.14      (![X34 : $i, X35 : $i]:
% 0.97/1.14         (~ (r2_hidden @ X34 @ X35) | ~ (r1_tarski @ X35 @ X34))),
% 0.97/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.97/1.14  thf('41', plain,
% 0.97/1.14      (((r2_hidden @ sk_B @ sk_A) | ~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 0.97/1.14      inference('sup-', [status(thm)], ['39', '40'])).
% 0.97/1.14  thf('42', plain,
% 0.97/1.14      ((((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.97/1.14        | (r2_hidden @ sk_B @ sk_A))),
% 0.97/1.14      inference('sup-', [status(thm)], ['16', '41'])).
% 0.97/1.14  thf('43', plain,
% 0.97/1.14      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 0.97/1.14        | ((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.97/1.14      inference('sup+', [status(thm)], ['14', '15'])).
% 0.97/1.14  thf('44', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.97/1.14      inference('sup-', [status(thm)], ['36', '37'])).
% 0.97/1.14  thf('45', plain,
% 0.97/1.14      ((((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.97/1.14        | (r2_hidden @ sk_A @ sk_B))),
% 0.97/1.14      inference('sup-', [status(thm)], ['43', '44'])).
% 0.97/1.14  thf(antisymmetry_r2_hidden, axiom,
% 0.97/1.14    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.97/1.14  thf('46', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.97/1.14      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.97/1.14  thf('47', plain,
% 0.97/1.14      ((((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.97/1.14        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.97/1.14      inference('sup-', [status(thm)], ['45', '46'])).
% 0.97/1.14  thf('48', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.97/1.14      inference('clc', [status(thm)], ['42', '47'])).
% 0.97/1.14  thf(t32_xboole_1, axiom,
% 0.97/1.14    (![A:$i,B:$i]:
% 0.97/1.14     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.97/1.14       ( ( A ) = ( B ) ) ))).
% 0.97/1.14  thf('49', plain,
% 0.97/1.14      (![X2 : $i, X3 : $i]:
% 0.97/1.14         (((X3) = (X2)) | ((k4_xboole_0 @ X3 @ X2) != (k4_xboole_0 @ X2 @ X3)))),
% 0.97/1.14      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.97/1.14  thf('50', plain,
% 0.97/1.14      ((((k4_xboole_0 @ sk_A @ sk_B) != (k1_xboole_0)) | ((sk_A) = (sk_B)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['48', '49'])).
% 0.97/1.14  thf('51', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.97/1.14      inference('sup+', [status(thm)], ['1', '2'])).
% 0.97/1.14  thf('52', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('53', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 0.97/1.14          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_tarski @ X0 @ X0)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.97/1.14  thf('54', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (r1_tarski @ X0 @ (k1_ordinal1 @ sk_A))
% 0.97/1.14          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k2_tarski @ sk_B @ sk_B)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['52', '53'])).
% 0.97/1.14  thf('55', plain,
% 0.97/1.14      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.97/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.14  thf('56', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (r1_tarski @ X0 @ (k1_ordinal1 @ sk_A))
% 0.97/1.14          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_B)))),
% 0.97/1.14      inference('demod', [status(thm)], ['54', '55'])).
% 0.97/1.14  thf('57', plain,
% 0.97/1.14      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_B))),
% 0.97/1.14      inference('sup-', [status(thm)], ['51', '56'])).
% 0.97/1.14  thf('58', plain,
% 0.97/1.14      (![X24 : $i, X25 : $i]:
% 0.97/1.14         (((X25) = (k1_tarski @ X24))
% 0.97/1.14          | ((X25) = (k1_xboole_0))
% 0.97/1.14          | ~ (r1_tarski @ X25 @ (k1_tarski @ X24)))),
% 0.97/1.14      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.97/1.14  thf('59', plain,
% 0.97/1.14      ((((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.97/1.14        | ((k4_xboole_0 @ sk_A @ sk_B) = (k1_tarski @ sk_B)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['57', '58'])).
% 0.97/1.14  thf('60', plain,
% 0.97/1.14      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.97/1.14      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.97/1.14  thf('61', plain,
% 0.97/1.14      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.97/1.14        | ((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.97/1.14      inference('sup+', [status(thm)], ['59', '60'])).
% 0.97/1.14  thf('62', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.97/1.14      inference('sup+', [status(thm)], ['5', '6'])).
% 0.97/1.14  thf('63', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.97/1.14      inference('sup+', [status(thm)], ['23', '24'])).
% 0.97/1.14  thf('64', plain,
% 0.97/1.14      (![X0 : $i]: (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_ordinal1 @ X0))),
% 0.97/1.14      inference('sup+', [status(thm)], ['62', '63'])).
% 0.97/1.14  thf('65', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('66', plain,
% 0.97/1.14      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.97/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.14  thf('67', plain,
% 0.97/1.14      (![X22 : $i, X23 : $i]:
% 0.97/1.14         ((r1_xboole_0 @ (k1_tarski @ X22) @ X23) | (r2_hidden @ X22 @ X23))),
% 0.97/1.14      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.97/1.14  thf('68', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         ((r1_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.97/1.14      inference('sup+', [status(thm)], ['66', '67'])).
% 0.97/1.14  thf('69', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 0.97/1.14          | ~ (r1_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0))
% 0.97/1.14          | (r1_tarski @ X1 @ X0))),
% 0.97/1.14      inference('sup-', [status(thm)], ['29', '30'])).
% 0.97/1.14  thf('70', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         ((r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.97/1.14          | (r1_tarski @ (k2_tarski @ X1 @ X1) @ X0)
% 0.97/1.14          | ~ (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k1_ordinal1 @ X0)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['68', '69'])).
% 0.97/1.14  thf('71', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_ordinal1 @ sk_A))
% 0.97/1.14          | (r1_tarski @ (k2_tarski @ X0 @ X0) @ sk_B)
% 0.97/1.14          | (r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_B)))),
% 0.97/1.14      inference('sup-', [status(thm)], ['65', '70'])).
% 0.97/1.14  thf('72', plain,
% 0.97/1.14      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.97/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.14  thf('73', plain,
% 0.97/1.14      (![X0 : $i]:
% 0.97/1.14         (~ (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_ordinal1 @ sk_A))
% 0.97/1.14          | (r1_tarski @ (k2_tarski @ X0 @ X0) @ sk_B)
% 0.97/1.14          | (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.97/1.14      inference('demod', [status(thm)], ['71', '72'])).
% 0.97/1.14  thf('74', plain,
% 0.97/1.14      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 0.97/1.14        | (r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B))),
% 0.97/1.14      inference('sup-', [status(thm)], ['64', '73'])).
% 0.97/1.14  thf('75', plain,
% 0.97/1.14      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.97/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.97/1.14  thf('76', plain,
% 0.97/1.14      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 0.97/1.14        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 0.97/1.14      inference('demod', [status(thm)], ['74', '75'])).
% 0.97/1.14  thf('77', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.97/1.14      inference('sup-', [status(thm)], ['36', '37'])).
% 0.97/1.14  thf('78', plain,
% 0.97/1.14      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 0.97/1.14      inference('sup-', [status(thm)], ['76', '77'])).
% 0.97/1.14  thf('79', plain,
% 0.97/1.14      (![X34 : $i, X35 : $i]:
% 0.97/1.14         (~ (r2_hidden @ X34 @ X35) | ~ (r1_tarski @ X35 @ X34))),
% 0.97/1.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.97/1.14  thf('80', plain,
% 0.97/1.14      (((r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.97/1.14      inference('sup-', [status(thm)], ['78', '79'])).
% 0.97/1.14  thf('81', plain,
% 0.97/1.14      ((((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.97/1.14        | (r2_hidden @ sk_A @ sk_B))),
% 0.97/1.14      inference('sup-', [status(thm)], ['61', '80'])).
% 0.97/1.14  thf('82', plain,
% 0.97/1.14      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.97/1.14        | ((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.97/1.14      inference('sup+', [status(thm)], ['59', '60'])).
% 0.97/1.14  thf('83', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]:
% 0.97/1.14         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.97/1.14      inference('sup-', [status(thm)], ['36', '37'])).
% 0.97/1.14  thf('84', plain,
% 0.97/1.14      ((((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.97/1.14        | (r2_hidden @ sk_B @ sk_A))),
% 0.97/1.14      inference('sup-', [status(thm)], ['82', '83'])).
% 0.97/1.14  thf('85', plain,
% 0.97/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.97/1.14      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.97/1.14  thf('86', plain,
% 0.97/1.14      ((((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.97/1.14        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.97/1.14      inference('sup-', [status(thm)], ['84', '85'])).
% 0.97/1.14  thf('87', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.97/1.14      inference('clc', [status(thm)], ['81', '86'])).
% 0.97/1.14  thf('88', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (sk_B)))),
% 0.97/1.14      inference('demod', [status(thm)], ['50', '87'])).
% 0.97/1.14  thf('89', plain, (((sk_A) = (sk_B))),
% 0.97/1.14      inference('simplify', [status(thm)], ['88'])).
% 0.97/1.14  thf('90', plain, (((sk_A) != (sk_B))),
% 0.97/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.14  thf('91', plain, ($false),
% 0.97/1.14      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 0.97/1.14  
% 0.97/1.14  % SZS output end Refutation
% 0.97/1.14  
% 0.97/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
