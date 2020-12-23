%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FlxMXP8sf5

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:27 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 118 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   21
%              Number of atoms          :  719 ( 952 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X54 @ X55 ) ) @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X42: $i] :
      ( ( ( k3_relat_1 @ X42 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X42: $i] :
      ( ( ( k3_relat_1 @ X42 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('11',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k3_tarski @ ( k2_tarski @ X5 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('20',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X43 ) @ X44 )
      | ( ( k8_relat_1 @ X44 @ X43 )
        = X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X56 @ X58 ) @ X57 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X56 @ X57 ) @ X58 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('25',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X54 @ X55 ) ) @ X55 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('26',plain,(
    ! [X42: $i] :
      ( ( ( k3_relat_1 @ X42 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ( v4_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ~ ( v4_relat_1 @ X47 @ X48 )
      | ( v4_relat_1 @ X47 @ X49 )
      | ~ ( r1_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v4_relat_1 @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( v4_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45
        = ( k7_relat_1 @ X45 @ X46 ) )
      | ~ ( v4_relat_1 @ X45 @ X46 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k2_wellord1 @ X0 @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('50',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k2_wellord1 @ X53 @ X52 )
        = ( k8_relat_1 @ X52 @ ( k7_relat_1 @ X53 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C @ sk_A ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C @ sk_A ) )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_wellord1 @ sk_C @ sk_A )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FlxMXP8sf5
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.73/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.73/0.90  % Solved by: fo/fo7.sh
% 0.73/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.90  % done 563 iterations in 0.443s
% 0.73/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.73/0.90  % SZS output start Refutation
% 0.73/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.73/0.90  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.73/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.73/0.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.73/0.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.73/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.73/0.90  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.73/0.90  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.73/0.90  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.73/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.73/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.73/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.73/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.90  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.73/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.73/0.90  thf(t29_wellord1, conjecture,
% 0.73/0.90    (![A:$i,B:$i,C:$i]:
% 0.73/0.90     ( ( v1_relat_1 @ C ) =>
% 0.73/0.90       ( ( r1_tarski @ A @ B ) =>
% 0.73/0.90         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.73/0.90           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.73/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.73/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.73/0.90        ( ( v1_relat_1 @ C ) =>
% 0.73/0.90          ( ( r1_tarski @ A @ B ) =>
% 0.73/0.90            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.73/0.90              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.73/0.90    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.73/0.90  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.73/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.90  thf(t20_wellord1, axiom,
% 0.73/0.90    (![A:$i,B:$i]:
% 0.73/0.90     ( ( v1_relat_1 @ B ) =>
% 0.73/0.90       ( ( r1_tarski @
% 0.73/0.90           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.73/0.90         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 0.73/0.90  thf('1', plain,
% 0.73/0.90      (![X54 : $i, X55 : $i]:
% 0.73/0.90         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X54 @ X55)) @ X55)
% 0.73/0.90          | ~ (v1_relat_1 @ X54))),
% 0.73/0.90      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.73/0.90  thf(t1_xboole_1, axiom,
% 0.73/0.90    (![A:$i,B:$i,C:$i]:
% 0.73/0.90     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.73/0.90       ( r1_tarski @ A @ C ) ))).
% 0.73/0.90  thf('2', plain,
% 0.73/0.90      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.73/0.90         (~ (r1_tarski @ X6 @ X7)
% 0.73/0.90          | ~ (r1_tarski @ X7 @ X8)
% 0.73/0.90          | (r1_tarski @ X6 @ X8))),
% 0.73/0.90      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.73/0.90  thf('3', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X1)
% 0.73/0.90          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.73/0.90          | ~ (r1_tarski @ X0 @ X2))),
% 0.73/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.73/0.90  thf('4', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.73/0.90          | ~ (v1_relat_1 @ X0))),
% 0.73/0.90      inference('sup-', [status(thm)], ['0', '3'])).
% 0.73/0.90  thf(d6_relat_1, axiom,
% 0.73/0.90    (![A:$i]:
% 0.73/0.90     ( ( v1_relat_1 @ A ) =>
% 0.73/0.90       ( ( k3_relat_1 @ A ) =
% 0.73/0.90         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.73/0.90  thf('5', plain,
% 0.73/0.90      (![X42 : $i]:
% 0.73/0.90         (((k3_relat_1 @ X42)
% 0.73/0.90            = (k2_xboole_0 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42)))
% 0.73/0.90          | ~ (v1_relat_1 @ X42))),
% 0.73/0.90      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.73/0.90  thf(l51_zfmisc_1, axiom,
% 0.73/0.90    (![A:$i,B:$i]:
% 0.73/0.90     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.73/0.90  thf('6', plain,
% 0.73/0.90      (![X38 : $i, X39 : $i]:
% 0.73/0.90         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.73/0.90      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.73/0.90  thf('7', plain,
% 0.73/0.90      (![X42 : $i]:
% 0.73/0.90         (((k3_relat_1 @ X42)
% 0.73/0.90            = (k3_tarski @ 
% 0.73/0.90               (k2_tarski @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))))
% 0.73/0.90          | ~ (v1_relat_1 @ X42))),
% 0.73/0.90      inference('demod', [status(thm)], ['5', '6'])).
% 0.73/0.90  thf(d10_xboole_0, axiom,
% 0.73/0.90    (![A:$i,B:$i]:
% 0.73/0.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.73/0.90  thf('8', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.73/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.73/0.90  thf('9', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.73/0.90      inference('simplify', [status(thm)], ['8'])).
% 0.73/0.90  thf(t10_xboole_1, axiom,
% 0.73/0.90    (![A:$i,B:$i,C:$i]:
% 0.73/0.90     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.73/0.90  thf('10', plain,
% 0.73/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.73/0.90         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.73/0.90      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.73/0.90  thf('11', plain,
% 0.73/0.90      (![X38 : $i, X39 : $i]:
% 0.73/0.90         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.73/0.90      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.73/0.90  thf('12', plain,
% 0.73/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.73/0.90         (~ (r1_tarski @ X3 @ X4)
% 0.73/0.90          | (r1_tarski @ X3 @ (k3_tarski @ (k2_tarski @ X5 @ X4))))),
% 0.73/0.90      inference('demod', [status(thm)], ['10', '11'])).
% 0.73/0.90  thf('13', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i]:
% 0.73/0.90         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.73/0.90      inference('sup-', [status(thm)], ['9', '12'])).
% 0.73/0.90  thf('14', plain,
% 0.73/0.90      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.73/0.90         (~ (r1_tarski @ X6 @ X7)
% 0.73/0.90          | ~ (r1_tarski @ X7 @ X8)
% 0.73/0.90          | (r1_tarski @ X6 @ X8))),
% 0.73/0.90      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.73/0.90  thf('15', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.90         ((r1_tarski @ X0 @ X2)
% 0.73/0.90          | ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2))),
% 0.73/0.90      inference('sup-', [status(thm)], ['13', '14'])).
% 0.73/0.90  thf('16', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i]:
% 0.73/0.90         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.73/0.90          | ~ (v1_relat_1 @ X0)
% 0.73/0.90          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.73/0.90      inference('sup-', [status(thm)], ['7', '15'])).
% 0.73/0.90  thf('17', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X0)
% 0.73/0.90          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.73/0.90          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.73/0.90      inference('sup-', [status(thm)], ['4', '16'])).
% 0.73/0.90  thf(dt_k2_wellord1, axiom,
% 0.73/0.90    (![A:$i,B:$i]:
% 0.73/0.90     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.73/0.90  thf('18', plain,
% 0.73/0.90      (![X50 : $i, X51 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k2_wellord1 @ X50 @ X51)))),
% 0.73/0.90      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.73/0.90  thf('19', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.73/0.90          | ~ (v1_relat_1 @ X0))),
% 0.73/0.90      inference('clc', [status(thm)], ['17', '18'])).
% 0.73/0.90  thf(t125_relat_1, axiom,
% 0.73/0.90    (![A:$i,B:$i]:
% 0.73/0.90     ( ( v1_relat_1 @ B ) =>
% 0.73/0.90       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.73/0.90         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.73/0.90  thf('20', plain,
% 0.73/0.90      (![X43 : $i, X44 : $i]:
% 0.73/0.90         (~ (r1_tarski @ (k2_relat_1 @ X43) @ X44)
% 0.73/0.90          | ((k8_relat_1 @ X44 @ X43) = (X43))
% 0.73/0.90          | ~ (v1_relat_1 @ X43))),
% 0.73/0.90      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.73/0.90  thf('21', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X0)
% 0.73/0.90          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.73/0.90          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.73/0.90              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.73/0.90      inference('sup-', [status(thm)], ['19', '20'])).
% 0.73/0.90  thf('22', plain,
% 0.73/0.90      (![X50 : $i, X51 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k2_wellord1 @ X50 @ X51)))),
% 0.73/0.90      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.73/0.90  thf('23', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.73/0.90            = (k2_wellord1 @ X0 @ sk_A))
% 0.73/0.90          | ~ (v1_relat_1 @ X0))),
% 0.73/0.90      inference('clc', [status(thm)], ['21', '22'])).
% 0.73/0.90  thf(t27_wellord1, axiom,
% 0.73/0.90    (![A:$i,B:$i,C:$i]:
% 0.73/0.90     ( ( v1_relat_1 @ C ) =>
% 0.73/0.90       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.73/0.90         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.73/0.90  thf('24', plain,
% 0.73/0.90      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.73/0.90         (((k2_wellord1 @ (k2_wellord1 @ X56 @ X58) @ X57)
% 0.73/0.90            = (k2_wellord1 @ (k2_wellord1 @ X56 @ X57) @ X58))
% 0.73/0.90          | ~ (v1_relat_1 @ X56))),
% 0.73/0.90      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.73/0.90  thf('25', plain,
% 0.73/0.90      (![X54 : $i, X55 : $i]:
% 0.73/0.90         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X54 @ X55)) @ X55)
% 0.73/0.90          | ~ (v1_relat_1 @ X54))),
% 0.73/0.90      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.73/0.90  thf('26', plain,
% 0.73/0.90      (![X42 : $i]:
% 0.73/0.90         (((k3_relat_1 @ X42)
% 0.73/0.90            = (k3_tarski @ 
% 0.73/0.90               (k2_tarski @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))))
% 0.73/0.90          | ~ (v1_relat_1 @ X42))),
% 0.73/0.90      inference('demod', [status(thm)], ['5', '6'])).
% 0.73/0.90  thf(t7_xboole_1, axiom,
% 0.73/0.90    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.73/0.90  thf('27', plain,
% 0.73/0.90      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.73/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.73/0.90  thf('28', plain,
% 0.73/0.90      (![X38 : $i, X39 : $i]:
% 0.73/0.90         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.73/0.90      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.73/0.90  thf('29', plain,
% 0.73/0.90      (![X9 : $i, X10 : $i]:
% 0.73/0.90         (r1_tarski @ X9 @ (k3_tarski @ (k2_tarski @ X9 @ X10)))),
% 0.73/0.90      inference('demod', [status(thm)], ['27', '28'])).
% 0.73/0.90  thf('30', plain,
% 0.73/0.90      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.73/0.90         (~ (r1_tarski @ X6 @ X7)
% 0.73/0.90          | ~ (r1_tarski @ X7 @ X8)
% 0.73/0.90          | (r1_tarski @ X6 @ X8))),
% 0.73/0.90      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.73/0.90  thf('31', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.90         ((r1_tarski @ X1 @ X2)
% 0.73/0.90          | ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2))),
% 0.73/0.90      inference('sup-', [status(thm)], ['29', '30'])).
% 0.73/0.90  thf('32', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i]:
% 0.73/0.90         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.73/0.90          | ~ (v1_relat_1 @ X0)
% 0.73/0.90          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.73/0.90      inference('sup-', [status(thm)], ['26', '31'])).
% 0.73/0.90  thf('33', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X1)
% 0.73/0.90          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.73/0.90          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 0.73/0.90      inference('sup-', [status(thm)], ['25', '32'])).
% 0.73/0.90  thf('34', plain,
% 0.73/0.90      (![X50 : $i, X51 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k2_wellord1 @ X50 @ X51)))),
% 0.73/0.90      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.73/0.90  thf('35', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i]:
% 0.73/0.90         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.73/0.90          | ~ (v1_relat_1 @ X1))),
% 0.73/0.90      inference('clc', [status(thm)], ['33', '34'])).
% 0.73/0.90  thf(d18_relat_1, axiom,
% 0.73/0.90    (![A:$i,B:$i]:
% 0.73/0.90     ( ( v1_relat_1 @ B ) =>
% 0.73/0.90       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.73/0.90  thf('36', plain,
% 0.73/0.90      (![X40 : $i, X41 : $i]:
% 0.73/0.90         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.73/0.90          | (v4_relat_1 @ X40 @ X41)
% 0.73/0.90          | ~ (v1_relat_1 @ X40))),
% 0.73/0.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.73/0.90  thf('37', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X1)
% 0.73/0.90          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0))
% 0.73/0.90          | (v4_relat_1 @ (k2_wellord1 @ X1 @ X0) @ X0))),
% 0.73/0.90      inference('sup-', [status(thm)], ['35', '36'])).
% 0.73/0.90  thf('38', plain,
% 0.73/0.90      (![X50 : $i, X51 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k2_wellord1 @ X50 @ X51)))),
% 0.73/0.90      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.73/0.90  thf('39', plain,
% 0.73/0.90      (![X0 : $i, X1 : $i]:
% 0.73/0.90         ((v4_relat_1 @ (k2_wellord1 @ X1 @ X0) @ X0) | ~ (v1_relat_1 @ X1))),
% 0.73/0.90      inference('clc', [status(thm)], ['37', '38'])).
% 0.73/0.90  thf('40', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.73/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.90  thf(t217_relat_1, axiom,
% 0.73/0.90    (![A:$i,B:$i]:
% 0.73/0.90     ( ( r1_tarski @ A @ B ) =>
% 0.73/0.90       ( ![C:$i]:
% 0.73/0.90         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.73/0.90           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.73/0.90  thf('41', plain,
% 0.73/0.90      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X47)
% 0.73/0.90          | ~ (v4_relat_1 @ X47 @ X48)
% 0.73/0.90          | (v4_relat_1 @ X47 @ X49)
% 0.73/0.90          | ~ (r1_tarski @ X48 @ X49))),
% 0.73/0.90      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.73/0.90  thf('42', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         ((v4_relat_1 @ X0 @ sk_B)
% 0.73/0.90          | ~ (v4_relat_1 @ X0 @ sk_A)
% 0.73/0.90          | ~ (v1_relat_1 @ X0))),
% 0.73/0.90      inference('sup-', [status(thm)], ['40', '41'])).
% 0.73/0.90  thf('43', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X0)
% 0.73/0.90          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.73/0.90          | (v4_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))),
% 0.73/0.90      inference('sup-', [status(thm)], ['39', '42'])).
% 0.73/0.90  thf('44', plain,
% 0.73/0.90      (![X50 : $i, X51 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k2_wellord1 @ X50 @ X51)))),
% 0.73/0.90      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.73/0.90  thf('45', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         ((v4_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B) | ~ (v1_relat_1 @ X0))),
% 0.73/0.90      inference('clc', [status(thm)], ['43', '44'])).
% 0.73/0.90  thf(t209_relat_1, axiom,
% 0.73/0.90    (![A:$i,B:$i]:
% 0.73/0.90     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.73/0.90       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.73/0.90  thf('46', plain,
% 0.73/0.90      (![X45 : $i, X46 : $i]:
% 0.73/0.90         (((X45) = (k7_relat_1 @ X45 @ X46))
% 0.73/0.90          | ~ (v4_relat_1 @ X45 @ X46)
% 0.73/0.90          | ~ (v1_relat_1 @ X45))),
% 0.73/0.90      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.73/0.90  thf('47', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X0)
% 0.73/0.90          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.73/0.90          | ((k2_wellord1 @ X0 @ sk_A)
% 0.73/0.90              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.73/0.90      inference('sup-', [status(thm)], ['45', '46'])).
% 0.73/0.90  thf('48', plain,
% 0.73/0.90      (![X50 : $i, X51 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k2_wellord1 @ X50 @ X51)))),
% 0.73/0.90      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.73/0.90  thf('49', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (((k2_wellord1 @ X0 @ sk_A)
% 0.73/0.90            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.73/0.90          | ~ (v1_relat_1 @ X0))),
% 0.73/0.90      inference('clc', [status(thm)], ['47', '48'])).
% 0.73/0.90  thf(t18_wellord1, axiom,
% 0.73/0.90    (![A:$i,B:$i]:
% 0.73/0.90     ( ( v1_relat_1 @ B ) =>
% 0.73/0.90       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.73/0.90  thf('50', plain,
% 0.73/0.90      (![X52 : $i, X53 : $i]:
% 0.73/0.90         (((k2_wellord1 @ X53 @ X52)
% 0.73/0.90            = (k8_relat_1 @ X52 @ (k7_relat_1 @ X53 @ X52)))
% 0.73/0.90          | ~ (v1_relat_1 @ X53))),
% 0.73/0.90      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.73/0.90  thf('51', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.73/0.90            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 0.73/0.90          | ~ (v1_relat_1 @ X0)
% 0.73/0.90          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.73/0.90      inference('sup+', [status(thm)], ['49', '50'])).
% 0.73/0.90  thf('52', plain,
% 0.73/0.90      (![X50 : $i, X51 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k2_wellord1 @ X50 @ X51)))),
% 0.73/0.90      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.73/0.90  thf('53', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X0)
% 0.73/0.90          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.73/0.90              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 0.73/0.90      inference('clc', [status(thm)], ['51', '52'])).
% 0.73/0.90  thf('54', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.73/0.90            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 0.73/0.90          | ~ (v1_relat_1 @ X0)
% 0.73/0.90          | ~ (v1_relat_1 @ X0))),
% 0.73/0.90      inference('sup+', [status(thm)], ['24', '53'])).
% 0.73/0.90  thf('55', plain,
% 0.73/0.90      (![X0 : $i]:
% 0.73/0.90         (~ (v1_relat_1 @ X0)
% 0.73/0.90          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.73/0.90              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 0.73/0.90      inference('simplify', [status(thm)], ['54'])).
% 0.73/0.90  thf('56', plain,
% 0.73/0.90      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.73/0.90         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.73/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.90  thf('57', plain,
% 0.73/0.90      ((((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C @ sk_A))
% 0.73/0.90          != (k2_wellord1 @ sk_C @ sk_A))
% 0.73/0.90        | ~ (v1_relat_1 @ sk_C))),
% 0.73/0.90      inference('sup-', [status(thm)], ['55', '56'])).
% 0.73/0.90  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.73/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.90  thf('59', plain,
% 0.73/0.90      (((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C @ sk_A))
% 0.73/0.90         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.73/0.90      inference('demod', [status(thm)], ['57', '58'])).
% 0.73/0.90  thf('60', plain,
% 0.73/0.90      ((((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))
% 0.73/0.90        | ~ (v1_relat_1 @ sk_C))),
% 0.73/0.90      inference('sup-', [status(thm)], ['23', '59'])).
% 0.73/0.90  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.73/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.90  thf('62', plain,
% 0.73/0.90      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.73/0.90      inference('demod', [status(thm)], ['60', '61'])).
% 0.73/0.90  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.73/0.90  
% 0.73/0.90  % SZS output end Refutation
% 0.73/0.90  
% 0.73/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
