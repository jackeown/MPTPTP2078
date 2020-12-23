%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OmOlmi6EUu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:25 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 394 expanded)
%              Number of leaves         :   38 ( 147 expanded)
%              Depth                    :   25
%              Number of atoms          :  928 (3011 expanded)
%              Number of equality atoms :   77 ( 290 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X63 @ X64 ) @ X65 )
        = ( k2_wellord1 @ X63 @ ( k3_xboole_0 @ X64 @ X65 ) ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

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

thf('1',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('8',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X42 ) @ X43 )
      | ( ( k8_relat_1 @ X43 @ X42 )
        = X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k2_wellord1 @ X58 @ X57 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X57 @ X58 ) @ X57 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X54 ) @ ( k6_relat_1 @ X53 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('16',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k7_relat_1 @ X47 @ X46 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X46 ) @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X50: $i] :
      ( ( ( k7_relat_1 @ X50 @ ( k1_relat_1 @ X50 ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','19','29','30'])).

thf('32',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X41: $i] :
      ( ( ( k3_relat_1 @ X41 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X41 ) @ ( k2_relat_1 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X41: $i] :
      ( ( ( k3_relat_1 @ X41 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X41 ) @ ( k1_relat_1 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k3_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( ( k3_relat_1 @ ( k6_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','19','29','30'])).

thf(t20_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf('49',plain,(
    ! [X61: $i,X62: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X61 @ X62 ) ) @ X62 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X61: $i,X62: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X61 @ X62 ) ) @ ( k3_relat_1 @ X61 ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','59'])).

thf('61',plain,(
    ! [X41: $i] :
      ( ( ( k3_relat_1 @ X41 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X41 ) @ ( k1_relat_1 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','19','29','30'])).

thf('70',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X63 @ X64 ) @ X65 )
        = ( k2_wellord1 @ X63 @ ( k3_xboole_0 @ X64 @ X65 ) ) )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('74',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X55 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','77'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('79',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X48 ) @ X49 )
      | ( ( k7_relat_1 @ X48 @ X49 )
        = X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) @ sk_B )
        = ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) @ sk_B )
      = ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ sk_A ) ),
    inference('sup+',[status(thm)],['31','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('86',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','19','29','30'])).

thf('91',plain,
    ( ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84','89','90'])).

thf('92',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X44: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('95',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['4','95'])).

thf('97',plain,(
    $false ),
    inference(simplify,[status(thm)],['96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OmOlmi6EUu
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:15:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.92  % Solved by: fo/fo7.sh
% 0.67/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.92  % done 810 iterations in 0.455s
% 0.67/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.92  % SZS output start Refutation
% 0.67/0.92  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.67/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.92  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.67/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.67/0.92  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.67/0.92  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.67/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.92  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.67/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.67/0.92  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.67/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.92  thf(t26_wellord1, axiom,
% 0.67/0.92    (![A:$i,B:$i,C:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ C ) =>
% 0.67/0.92       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.67/0.92         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.67/0.92  thf('0', plain,
% 0.67/0.92      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.67/0.92         (((k2_wellord1 @ (k2_wellord1 @ X63 @ X64) @ X65)
% 0.67/0.92            = (k2_wellord1 @ X63 @ (k3_xboole_0 @ X64 @ X65)))
% 0.67/0.92          | ~ (v1_relat_1 @ X63))),
% 0.67/0.92      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.67/0.92  thf(t29_wellord1, conjecture,
% 0.67/0.92    (![A:$i,B:$i,C:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ C ) =>
% 0.67/0.92       ( ( r1_tarski @ A @ B ) =>
% 0.67/0.92         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.67/0.92           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.67/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.67/0.92        ( ( v1_relat_1 @ C ) =>
% 0.67/0.92          ( ( r1_tarski @ A @ B ) =>
% 0.67/0.92            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.67/0.92              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.67/0.92    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.67/0.92  thf('1', plain,
% 0.67/0.92      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.67/0.92         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('2', plain,
% 0.67/0.92      ((((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.67/0.92          != (k2_wellord1 @ sk_C @ sk_A))
% 0.67/0.92        | ~ (v1_relat_1 @ sk_C))),
% 0.67/0.92      inference('sup-', [status(thm)], ['0', '1'])).
% 0.67/0.92  thf('3', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('4', plain,
% 0.67/0.92      (((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.67/0.92         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.67/0.92  thf(t71_relat_1, axiom,
% 0.67/0.92    (![A:$i]:
% 0.67/0.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.67/0.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.67/0.92  thf('5', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.67/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.92  thf(d10_xboole_0, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.92  thf('6', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.67/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.92  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.67/0.92      inference('simplify', [status(thm)], ['6'])).
% 0.67/0.92  thf(t125_relat_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ B ) =>
% 0.67/0.92       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.67/0.92         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.67/0.92  thf('8', plain,
% 0.67/0.92      (![X42 : $i, X43 : $i]:
% 0.67/0.92         (~ (r1_tarski @ (k2_relat_1 @ X42) @ X43)
% 0.67/0.92          | ((k8_relat_1 @ X43 @ X42) = (X42))
% 0.67/0.92          | ~ (v1_relat_1 @ X42))),
% 0.67/0.92      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.67/0.92  thf('9', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.67/0.92  thf('10', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.67/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['5', '9'])).
% 0.67/0.92  thf(fc3_funct_1, axiom,
% 0.67/0.92    (![A:$i]:
% 0.67/0.92     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.67/0.92       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.67/0.92  thf('11', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.67/0.92  thf('12', plain,
% 0.67/0.92      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['10', '11'])).
% 0.67/0.92  thf(t17_wellord1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ B ) =>
% 0.67/0.92       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.67/0.92  thf('13', plain,
% 0.67/0.92      (![X57 : $i, X58 : $i]:
% 0.67/0.92         (((k2_wellord1 @ X58 @ X57)
% 0.67/0.92            = (k7_relat_1 @ (k8_relat_1 @ X57 @ X58) @ X57))
% 0.67/0.92          | ~ (v1_relat_1 @ X58))),
% 0.67/0.92      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.67/0.92  thf('14', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (((k2_wellord1 @ (k6_relat_1 @ X0) @ X0)
% 0.67/0.92            = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.67/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['12', '13'])).
% 0.67/0.92  thf(t43_funct_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.67/0.92       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.67/0.92  thf('15', plain,
% 0.67/0.92      (![X53 : $i, X54 : $i]:
% 0.67/0.92         ((k5_relat_1 @ (k6_relat_1 @ X54) @ (k6_relat_1 @ X53))
% 0.67/0.92           = (k6_relat_1 @ (k3_xboole_0 @ X53 @ X54)))),
% 0.67/0.92      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.67/0.92  thf(t94_relat_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ B ) =>
% 0.67/0.92       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.67/0.92  thf('16', plain,
% 0.67/0.92      (![X46 : $i, X47 : $i]:
% 0.67/0.92         (((k7_relat_1 @ X47 @ X46) = (k5_relat_1 @ (k6_relat_1 @ X46) @ X47))
% 0.67/0.92          | ~ (v1_relat_1 @ X47))),
% 0.67/0.92      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.67/0.92  thf('17', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.67/0.92            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.67/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['15', '16'])).
% 0.67/0.92  thf('18', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.67/0.92  thf('19', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.67/0.92           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.92  thf('20', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.67/0.92           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.92  thf(t98_relat_1, axiom,
% 0.67/0.92    (![A:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ A ) =>
% 0.67/0.92       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.67/0.92  thf('21', plain,
% 0.67/0.92      (![X50 : $i]:
% 0.67/0.92         (((k7_relat_1 @ X50 @ (k1_relat_1 @ X50)) = (X50))
% 0.67/0.92          | ~ (v1_relat_1 @ X50))),
% 0.67/0.92      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.67/0.92  thf('22', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (((k6_relat_1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.67/0.92            = (k6_relat_1 @ X0))
% 0.67/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['20', '21'])).
% 0.67/0.92  thf('23', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.67/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.92  thf('24', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.67/0.92  thf('25', plain,
% 0.67/0.92      (![X0 : $i]: ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X0)) = (k6_relat_1 @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.67/0.92  thf('26', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.67/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.92  thf('27', plain,
% 0.67/0.92      (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['25', '26'])).
% 0.67/0.92  thf('28', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.67/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.92  thf('29', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['27', '28'])).
% 0.67/0.92  thf('30', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.67/0.92  thf('31', plain,
% 0.67/0.92      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['14', '19', '29', '30'])).
% 0.67/0.92  thf('32', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.67/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.92  thf('33', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.67/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.92  thf(d6_relat_1, axiom,
% 0.67/0.92    (![A:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ A ) =>
% 0.67/0.92       ( ( k3_relat_1 @ A ) =
% 0.67/0.92         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.67/0.92  thf('34', plain,
% 0.67/0.92      (![X41 : $i]:
% 0.67/0.92         (((k3_relat_1 @ X41)
% 0.67/0.92            = (k2_xboole_0 @ (k1_relat_1 @ X41) @ (k2_relat_1 @ X41)))
% 0.67/0.92          | ~ (v1_relat_1 @ X41))),
% 0.67/0.92      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.67/0.92  thf(commutativity_k2_tarski, axiom,
% 0.67/0.92    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.67/0.92  thf('35', plain,
% 0.67/0.92      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.67/0.92  thf(l51_zfmisc_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.67/0.92  thf('36', plain,
% 0.67/0.92      (![X37 : $i, X38 : $i]:
% 0.67/0.92         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.67/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.67/0.92  thf('37', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('sup+', [status(thm)], ['35', '36'])).
% 0.67/0.92  thf('38', plain,
% 0.67/0.92      (![X37 : $i, X38 : $i]:
% 0.67/0.92         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.67/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.67/0.92  thf('39', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('sup+', [status(thm)], ['37', '38'])).
% 0.67/0.92  thf('40', plain,
% 0.67/0.92      (![X41 : $i]:
% 0.67/0.92         (((k3_relat_1 @ X41)
% 0.67/0.92            = (k2_xboole_0 @ (k2_relat_1 @ X41) @ (k1_relat_1 @ X41)))
% 0.67/0.92          | ~ (v1_relat_1 @ X41))),
% 0.67/0.92      inference('demod', [status(thm)], ['34', '39'])).
% 0.67/0.92  thf(t7_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.67/0.92  thf('41', plain,
% 0.67/0.92      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.67/0.92      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.67/0.92  thf('42', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.67/0.92          | ~ (v1_relat_1 @ X0))),
% 0.67/0.92      inference('sup+', [status(thm)], ['40', '41'])).
% 0.67/0.92  thf('43', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((r1_tarski @ X0 @ (k3_relat_1 @ (k6_relat_1 @ X0)))
% 0.67/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['33', '42'])).
% 0.67/0.92  thf('44', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.67/0.92  thf('45', plain,
% 0.67/0.92      (![X0 : $i]: (r1_tarski @ X0 @ (k3_relat_1 @ (k6_relat_1 @ X0)))),
% 0.67/0.92      inference('demod', [status(thm)], ['43', '44'])).
% 0.67/0.92  thf('46', plain,
% 0.67/0.92      (![X0 : $i, X2 : $i]:
% 0.67/0.92         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.92  thf('47', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (~ (r1_tarski @ (k3_relat_1 @ (k6_relat_1 @ X0)) @ X0)
% 0.67/0.92          | ((k3_relat_1 @ (k6_relat_1 @ X0)) = (X0)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['45', '46'])).
% 0.67/0.92  thf('48', plain,
% 0.67/0.92      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['14', '19', '29', '30'])).
% 0.67/0.92  thf(t20_wellord1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ B ) =>
% 0.67/0.92       ( ( r1_tarski @
% 0.67/0.92           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.67/0.92         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 0.67/0.92  thf('49', plain,
% 0.67/0.92      (![X61 : $i, X62 : $i]:
% 0.67/0.92         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X61 @ X62)) @ X62)
% 0.67/0.92          | ~ (v1_relat_1 @ X61))),
% 0.67/0.92      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.67/0.92  thf('50', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((r1_tarski @ (k3_relat_1 @ (k6_relat_1 @ X0)) @ X0)
% 0.67/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['48', '49'])).
% 0.67/0.92  thf('51', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.67/0.92  thf('52', plain,
% 0.67/0.92      (![X0 : $i]: (r1_tarski @ (k3_relat_1 @ (k6_relat_1 @ X0)) @ X0)),
% 0.67/0.92      inference('demod', [status(thm)], ['50', '51'])).
% 0.67/0.92  thf('53', plain, (![X0 : $i]: ((k3_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['47', '52'])).
% 0.67/0.92  thf('54', plain,
% 0.67/0.92      (![X61 : $i, X62 : $i]:
% 0.67/0.92         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X61 @ X62)) @ 
% 0.67/0.92           (k3_relat_1 @ X61))
% 0.67/0.92          | ~ (v1_relat_1 @ X61))),
% 0.67/0.92      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.67/0.92  thf('55', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.67/0.92           X0)
% 0.67/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['53', '54'])).
% 0.67/0.92  thf('56', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.67/0.92  thf('57', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.67/0.92          X0)),
% 0.67/0.92      inference('demod', [status(thm)], ['55', '56'])).
% 0.67/0.92  thf(t1_xboole_1, axiom,
% 0.67/0.92    (![A:$i,B:$i,C:$i]:
% 0.67/0.92     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.67/0.92       ( r1_tarski @ A @ C ) ))).
% 0.67/0.92  thf('58', plain,
% 0.67/0.92      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.92         (~ (r1_tarski @ X3 @ X4)
% 0.67/0.92          | ~ (r1_tarski @ X4 @ X5)
% 0.67/0.92          | (r1_tarski @ X3 @ X5))),
% 0.67/0.92      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.67/0.92  thf('59', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.92         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 0.67/0.92           X2)
% 0.67/0.92          | ~ (r1_tarski @ X0 @ X2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['57', '58'])).
% 0.67/0.92  thf('60', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (r1_tarski @ 
% 0.67/0.92          (k3_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)) @ sk_B)),
% 0.67/0.92      inference('sup-', [status(thm)], ['32', '59'])).
% 0.67/0.92  thf('61', plain,
% 0.67/0.92      (![X41 : $i]:
% 0.67/0.92         (((k3_relat_1 @ X41)
% 0.67/0.92            = (k2_xboole_0 @ (k2_relat_1 @ X41) @ (k1_relat_1 @ X41)))
% 0.67/0.92          | ~ (v1_relat_1 @ X41))),
% 0.67/0.92      inference('demod', [status(thm)], ['34', '39'])).
% 0.67/0.92  thf('62', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('sup+', [status(thm)], ['37', '38'])).
% 0.67/0.92  thf('63', plain,
% 0.67/0.92      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.67/0.92      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.67/0.92  thf('64', plain,
% 0.67/0.92      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.92         (~ (r1_tarski @ X3 @ X4)
% 0.67/0.92          | ~ (r1_tarski @ X4 @ X5)
% 0.67/0.92          | (r1_tarski @ X3 @ X5))),
% 0.67/0.92      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.67/0.92  thf('65', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.92         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['63', '64'])).
% 0.67/0.92  thf('66', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.92         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 0.67/0.92      inference('sup-', [status(thm)], ['62', '65'])).
% 0.67/0.92  thf('67', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.67/0.92          | ~ (v1_relat_1 @ X0)
% 0.67/0.92          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.67/0.92      inference('sup-', [status(thm)], ['61', '66'])).
% 0.67/0.92  thf('68', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((r1_tarski @ 
% 0.67/0.92           (k1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)) @ sk_B)
% 0.67/0.92          | ~ (v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['60', '67'])).
% 0.67/0.92  thf('69', plain,
% 0.67/0.92      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['14', '19', '29', '30'])).
% 0.67/0.92  thf('70', plain,
% 0.67/0.92      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.67/0.92         (((k2_wellord1 @ (k2_wellord1 @ X63 @ X64) @ X65)
% 0.67/0.92            = (k2_wellord1 @ X63 @ (k3_xboole_0 @ X64 @ X65)))
% 0.67/0.92          | ~ (v1_relat_1 @ X63))),
% 0.67/0.92      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.67/0.92  thf('71', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         (((k2_wellord1 @ (k6_relat_1 @ X0) @ X1)
% 0.67/0.92            = (k2_wellord1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.67/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['69', '70'])).
% 0.67/0.92  thf('72', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.67/0.92  thf('73', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k2_wellord1 @ (k6_relat_1 @ X0) @ X1)
% 0.67/0.92           = (k2_wellord1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.67/0.92      inference('demod', [status(thm)], ['71', '72'])).
% 0.67/0.92  thf(dt_k2_wellord1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.67/0.92  thf('74', plain,
% 0.67/0.92      (![X55 : $i, X56 : $i]:
% 0.67/0.92         (~ (v1_relat_1 @ X55) | (v1_relat_1 @ (k2_wellord1 @ X55 @ X56)))),
% 0.67/0.92      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.67/0.92  thf('75', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X1) @ X0))
% 0.67/0.92          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.67/0.92      inference('sup+', [status(thm)], ['73', '74'])).
% 0.67/0.92  thf('76', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 0.67/0.92      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.67/0.92  thf('77', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         (v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X1) @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['75', '76'])).
% 0.67/0.92  thf('78', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (r1_tarski @ 
% 0.67/0.92          (k1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)) @ sk_B)),
% 0.67/0.92      inference('demod', [status(thm)], ['68', '77'])).
% 0.67/0.92  thf(t97_relat_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( v1_relat_1 @ B ) =>
% 0.67/0.92       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.67/0.92         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.67/0.92  thf('79', plain,
% 0.67/0.92      (![X48 : $i, X49 : $i]:
% 0.67/0.92         (~ (r1_tarski @ (k1_relat_1 @ X48) @ X49)
% 0.67/0.92          | ((k7_relat_1 @ X48 @ X49) = (X48))
% 0.67/0.92          | ~ (v1_relat_1 @ X48))),
% 0.67/0.92      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.67/0.92  thf('80', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         (~ (v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0))
% 0.67/0.92          | ((k7_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0) @ sk_B)
% 0.67/0.92              = (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)))),
% 0.67/0.92      inference('sup-', [status(thm)], ['78', '79'])).
% 0.67/0.92  thf('81', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         (v1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ X1) @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['75', '76'])).
% 0.67/0.92  thf('82', plain,
% 0.67/0.92      (![X0 : $i]:
% 0.67/0.92         ((k7_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0) @ sk_B)
% 0.67/0.92           = (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['80', '81'])).
% 0.67/0.92  thf('83', plain,
% 0.67/0.92      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.67/0.92         = (k2_wellord1 @ (k6_relat_1 @ sk_A) @ sk_A))),
% 0.67/0.92      inference('sup+', [status(thm)], ['31', '82'])).
% 0.67/0.92  thf('84', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.67/0.92           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.67/0.92      inference('demod', [status(thm)], ['17', '18'])).
% 0.67/0.92  thf('85', plain,
% 0.67/0.92      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.67/0.92      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.67/0.92  thf(t12_setfam_1, axiom,
% 0.67/0.92    (![A:$i,B:$i]:
% 0.67/0.92     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.67/0.92  thf('86', plain,
% 0.67/0.92      (![X39 : $i, X40 : $i]:
% 0.67/0.92         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.67/0.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.67/0.92  thf('87', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]:
% 0.67/0.92         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('sup+', [status(thm)], ['85', '86'])).
% 0.67/0.92  thf('88', plain,
% 0.67/0.92      (![X39 : $i, X40 : $i]:
% 0.67/0.92         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.67/0.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.67/0.92  thf('89', plain,
% 0.67/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.92      inference('sup+', [status(thm)], ['87', '88'])).
% 0.67/0.92  thf('90', plain,
% 0.67/0.92      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.67/0.92      inference('demod', [status(thm)], ['14', '19', '29', '30'])).
% 0.67/0.92  thf('91', plain,
% 0.67/0.92      (((k6_relat_1 @ (k3_xboole_0 @ sk_B @ sk_A)) = (k6_relat_1 @ sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['83', '84', '89', '90'])).
% 0.67/0.92  thf('92', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.67/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.92  thf('93', plain,
% 0.67/0.92      (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.67/0.92      inference('sup+', [status(thm)], ['91', '92'])).
% 0.67/0.92  thf('94', plain, (![X44 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.67/0.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.92  thf('95', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['93', '94'])).
% 0.67/0.92  thf('96', plain,
% 0.67/0.92      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.67/0.92      inference('demod', [status(thm)], ['4', '95'])).
% 0.67/0.92  thf('97', plain, ($false), inference('simplify', [status(thm)], ['96'])).
% 0.67/0.92  
% 0.67/0.92  % SZS output end Refutation
% 0.67/0.92  
% 0.67/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
