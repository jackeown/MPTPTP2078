%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y7CQxLtjHG

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:42 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 239 expanded)
%              Number of leaves         :   26 (  80 expanded)
%              Depth                    :   20
%              Number of atoms          :  717 (1763 expanded)
%              Number of equality atoms :   64 ( 173 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X50: $i] :
      ( ( k1_ordinal1 @ X50 )
      = ( k2_xboole_0 @ X50 @ ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('4',plain,(
    ! [X51: $i] :
      ( r2_hidden @ X51 @ ( k1_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('5',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X42: $i,X44: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X42 ) @ X44 )
      | ~ ( r2_hidden @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k4_xboole_0 @ X48 @ ( k1_tarski @ X49 ) )
        = X48 )
      | ( r2_hidden @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('18',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X47 @ X48 )
      | ( ( k4_xboole_0 @ X48 @ ( k1_tarski @ X47 ) )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('26',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r2_hidden @ X42 @ X43 )
      | ~ ( r1_tarski @ ( k1_tarski @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['18','28'])).

thf('30',plain,(
    ! [X42: $i,X44: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X42 ) @ X44 )
      | ~ ( r2_hidden @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('33',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X42: $i,X44: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X42 ) @ X44 )
      | ~ ( r2_hidden @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k4_xboole_0 @ X48 @ ( k1_tarski @ X49 ) )
        = X48 )
      | ( r2_hidden @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('40',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X51: $i] :
      ( r2_hidden @ X51 @ ( k1_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('44',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ) ),
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

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_xboole_0 @ ( k1_ordinal1 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_B ) ) @ sk_A )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['18','28'])).

thf('51',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['49','50'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('53',plain,
    ( ( r2_hidden @ sk_B @ sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('55',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('58',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('59',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17 = X16 )
      | ( ( k4_xboole_0 @ X17 @ X16 )
       != ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
       != k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('70',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( sk_B
    = ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('77',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y7CQxLtjHG
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:02 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 934 iterations in 0.342s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.77  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.58/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.77  thf(d1_ordinal1, axiom,
% 0.58/0.77    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      (![X50 : $i]:
% 0.58/0.77         ((k1_ordinal1 @ X50) = (k2_xboole_0 @ X50 @ (k1_tarski @ X50)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.58/0.77  thf(t40_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.58/0.77           = (k4_xboole_0 @ X20 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0))
% 0.58/0.77           = (k4_xboole_0 @ X0 @ (k1_tarski @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['0', '1'])).
% 0.58/0.77  thf(t12_ordinal1, conjecture,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i,B:$i]:
% 0.58/0.77        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 0.58/0.77  thf('3', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.58/0.77  thf('4', plain, (![X51 : $i]: (r2_hidden @ X51 @ (k1_ordinal1 @ X51))),
% 0.58/0.77      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.58/0.77  thf('5', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.58/0.77      inference('sup+', [status(thm)], ['3', '4'])).
% 0.58/0.77  thf(d5_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.58/0.77       ( ![D:$i]:
% 0.58/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.77           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X2 @ X3)
% 0.58/0.77          | (r2_hidden @ X2 @ X4)
% 0.58/0.77          | (r2_hidden @ X2 @ X5)
% 0.58/0.77          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.77         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.58/0.77          | (r2_hidden @ X2 @ X4)
% 0.58/0.77          | ~ (r2_hidden @ X2 @ X3))),
% 0.58/0.77      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.77  thf('8', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r2_hidden @ sk_B @ X0)
% 0.58/0.77          | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['5', '7'])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_A)))
% 0.58/0.77        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['2', '8'])).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X6 @ X5)
% 0.58/0.77          | (r2_hidden @ X6 @ X3)
% 0.58/0.77          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.58/0.77         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['10'])).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['9', '11'])).
% 0.58/0.77  thf(l1_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (![X42 : $i, X44 : $i]:
% 0.58/0.77         ((r1_tarski @ (k1_tarski @ X42) @ X44) | ~ (r2_hidden @ X42 @ X44))),
% 0.58/0.77      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ sk_A)
% 0.58/0.77        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.77  thf(l32_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (![X13 : $i, X15 : $i]:
% 0.58/0.77         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.58/0.77          | ~ (r1_tarski @ X13 @ X15))),
% 0.58/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ sk_A)
% 0.58/0.77        | ((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.58/0.77            = (k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.77  thf(t65_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.58/0.77       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      (![X48 : $i, X49 : $i]:
% 0.58/0.77         (((k4_xboole_0 @ X48 @ (k1_tarski @ X49)) = (X48))
% 0.58/0.77          | (r2_hidden @ X49 @ X48))),
% 0.58/0.77      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      ((((k1_xboole_0) = (k1_tarski @ sk_B))
% 0.58/0.77        | (r2_hidden @ sk_B @ sk_A)
% 0.58/0.77        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['16', '17'])).
% 0.58/0.77  thf(d10_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.77  thf('20', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.58/0.77      inference('simplify', [status(thm)], ['19'])).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      (![X13 : $i, X15 : $i]:
% 0.58/0.77         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.58/0.77          | ~ (r1_tarski @ X13 @ X15))),
% 0.58/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.77  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('23', plain,
% 0.58/0.77      (![X47 : $i, X48 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X47 @ X48)
% 0.58/0.77          | ((k4_xboole_0 @ X48 @ (k1_tarski @ X47)) != (X48)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.58/0.77          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.77  thf('25', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.58/0.77      inference('simplify', [status(thm)], ['19'])).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (![X42 : $i, X43 : $i]:
% 0.58/0.77         ((r2_hidden @ X42 @ X43) | ~ (r1_tarski @ (k1_tarski @ X42) @ X43))),
% 0.58/0.77      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.77  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.77  thf('28', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['24', '27'])).
% 0.58/0.77  thf('29', plain,
% 0.58/0.77      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_B @ sk_A))),
% 0.58/0.77      inference('clc', [status(thm)], ['18', '28'])).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      (![X42 : $i, X44 : $i]:
% 0.58/0.77         ((r1_tarski @ (k1_tarski @ X42) @ X44) | ~ (r2_hidden @ X42 @ X44))),
% 0.58/0.77      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.77  thf('31', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ sk_A)
% 0.58/0.77        | (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ sk_A)
% 0.58/0.77        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.77  thf('33', plain,
% 0.58/0.77      (![X10 : $i, X12 : $i]:
% 0.58/0.77         (((X10) = (X12))
% 0.58/0.77          | ~ (r1_tarski @ X12 @ X10)
% 0.58/0.77          | ~ (r1_tarski @ X10 @ X12))),
% 0.58/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ sk_A)
% 0.58/0.77        | ~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.58/0.77        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('35', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ sk_A)
% 0.58/0.77        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B))
% 0.58/0.77        | (r2_hidden @ sk_B @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['31', '34'])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (k1_tarski @ sk_B)) | (r2_hidden @ sk_B @ sk_A))),
% 0.58/0.77      inference('simplify', [status(thm)], ['35'])).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (![X42 : $i, X44 : $i]:
% 0.58/0.77         ((r1_tarski @ (k1_tarski @ X42) @ X44) | ~ (r2_hidden @ X42 @ X44))),
% 0.58/0.77      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.77  thf('38', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (k1_tarski @ sk_B))
% 0.58/0.77        | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.77  thf('39', plain,
% 0.58/0.77      (![X48 : $i, X49 : $i]:
% 0.58/0.77         (((k4_xboole_0 @ X48 @ (k1_tarski @ X49)) = (X48))
% 0.58/0.77          | (r2_hidden @ X49 @ X48))),
% 0.58/0.77      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.58/0.77  thf('40', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('41', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0))
% 0.58/0.77           = (k4_xboole_0 @ X0 @ (k1_tarski @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['0', '1'])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      (((k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_B))
% 0.58/0.77         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_B)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['40', '41'])).
% 0.58/0.77  thf('43', plain, (![X51 : $i]: (r2_hidden @ X51 @ (k1_ordinal1 @ X51))),
% 0.58/0.77      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.58/0.77  thf('44', plain,
% 0.58/0.77      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.77         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.58/0.77          | (r2_hidden @ X2 @ X4)
% 0.58/0.77          | ~ (r2_hidden @ X2 @ X3))),
% 0.58/0.77      inference('simplify', [status(thm)], ['6'])).
% 0.58/0.77  thf('45', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((r2_hidden @ X0 @ X1)
% 0.58/0.77          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_ordinal1 @ X0) @ X1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['43', '44'])).
% 0.58/0.77  thf(antisymmetry_r2_hidden, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.58/0.77  thf('46', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.58/0.77      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((r2_hidden @ X1 @ X0)
% 0.58/0.77          | ~ (r2_hidden @ (k4_xboole_0 @ (k1_ordinal1 @ X1) @ X0) @ X1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.77  thf('48', plain,
% 0.58/0.77      ((~ (r2_hidden @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_B)) @ sk_A)
% 0.58/0.77        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['42', '47'])).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.58/0.77        | (r2_hidden @ sk_B @ sk_B)
% 0.58/0.77        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['39', '48'])).
% 0.58/0.77  thf('50', plain,
% 0.58/0.77      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_B @ sk_A))),
% 0.58/0.77      inference('clc', [status(thm)], ['18', '28'])).
% 0.58/0.77  thf('51', plain,
% 0.58/0.77      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_B @ sk_B))),
% 0.58/0.77      inference('clc', [status(thm)], ['49', '50'])).
% 0.58/0.77  thf(t7_ordinal1, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.77  thf('52', plain,
% 0.58/0.77      (![X52 : $i, X53 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.77  thf('53', plain,
% 0.58/0.77      (((r2_hidden @ sk_B @ sk_B) | ~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['51', '52'])).
% 0.58/0.77  thf('54', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (k1_tarski @ sk_B)) | (r2_hidden @ sk_B @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['38', '53'])).
% 0.58/0.77  thf('55', plain,
% 0.58/0.77      (![X52 : $i, X53 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      ((((k1_tarski @ sk_A) = (k1_tarski @ sk_B)) | ~ (r1_tarski @ sk_B @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.77  thf('57', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.58/0.77      inference('simplify', [status(thm)], ['19'])).
% 0.58/0.77  thf('58', plain, (((k1_tarski @ sk_A) = (k1_tarski @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['56', '57'])).
% 0.58/0.77  thf(t69_enumset1, axiom,
% 0.58/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.77  thf('59', plain,
% 0.58/0.77      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.58/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.77  thf(l51_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('60', plain,
% 0.58/0.77      (![X45 : $i, X46 : $i]:
% 0.58/0.77         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.58/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.77  thf('61', plain,
% 0.58/0.77      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['59', '60'])).
% 0.58/0.77  thf('62', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.58/0.77           = (k4_xboole_0 @ X20 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.58/0.77  thf('63', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ (k3_tarski @ (k1_tarski @ X0)) @ X0)
% 0.58/0.77           = (k4_xboole_0 @ X0 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['61', '62'])).
% 0.58/0.77  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('65', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ (k3_tarski @ (k1_tarski @ X0)) @ X0) = (k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['63', '64'])).
% 0.58/0.77  thf(t32_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.58/0.77       ( ( A ) = ( B ) ) ))).
% 0.58/0.77  thf('66', plain,
% 0.58/0.77      (![X16 : $i, X17 : $i]:
% 0.58/0.77         (((X17) = (X16))
% 0.58/0.77          | ((k4_xboole_0 @ X17 @ X16) != (k4_xboole_0 @ X16 @ X17)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.58/0.77  thf('67', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k4_xboole_0 @ X0 @ (k3_tarski @ (k1_tarski @ X0))) != (k1_xboole_0))
% 0.58/0.77          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.77  thf('68', plain,
% 0.58/0.77      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['59', '60'])).
% 0.58/0.77  thf(t7_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('69', plain,
% 0.58/0.77      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.77  thf('70', plain,
% 0.58/0.77      (![X13 : $i, X15 : $i]:
% 0.58/0.77         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.58/0.77          | ~ (r1_tarski @ X13 @ X15))),
% 0.58/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.58/0.77  thf('71', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['69', '70'])).
% 0.58/0.77  thf('72', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ X0 @ (k3_tarski @ (k1_tarski @ X0))) = (k1_xboole_0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['68', '71'])).
% 0.58/0.77  thf('73', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.77          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 0.58/0.77      inference('demod', [status(thm)], ['67', '72'])).
% 0.58/0.77  thf('74', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['73'])).
% 0.58/0.77  thf('75', plain, (((sk_B) = (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['58', '74'])).
% 0.58/0.77  thf('76', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['73'])).
% 0.58/0.77  thf('77', plain, (((sk_B) = (sk_A))),
% 0.58/0.77      inference('demod', [status(thm)], ['75', '76'])).
% 0.58/0.77  thf('78', plain, (((sk_A) != (sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('79', plain, ($false),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
