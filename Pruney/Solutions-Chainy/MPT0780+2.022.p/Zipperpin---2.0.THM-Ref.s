%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Udgrrg3EX3

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:28 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 224 expanded)
%              Number of leaves         :   27 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  892 (1780 expanded)
%              Number of equality atoms :   63 ( 143 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X40 @ X41 ) @ X42 )
        = ( k2_wellord1 @ X40 @ ( k3_xboole_0 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k8_relat_1 @ X20 @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_wellord1 @ X39 @ X38 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X38 @ X39 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('13',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k8_relat_1 @ X20 @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_wellord1 @ X39 @ X38 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X38 @ X39 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('20',plain,
    ( ( ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_wellord1 @ X39 @ X38 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X38 @ X39 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('29',plain,(
    ! [X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ ( k1_relat_1 @ X31 ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','32','33'])).

thf('35',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_wellord1 @ X39 @ X38 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X38 @ X39 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k7_relat_1 @ X29 @ X30 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','32','33'])).

thf('50',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('53',plain,
    ( ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','51','52'])).

thf('54',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X40 @ X41 ) @ X42 )
        = ( k2_wellord1 @ X40 @ ( k3_xboole_0 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 )
      = ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ) @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','61'])).

thf('63',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('65',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('67',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('68',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','32','33'])).

thf('72',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X40 @ X41 ) @ X42 )
        = ( k2_wellord1 @ X40 @ ( k3_xboole_0 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('73',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X43 @ X45 ) @ X44 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X43 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('74',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X43 @ X45 ) @ X44 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X43 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) ) @ X1 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['72','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['71','82'])).

thf('84',plain,(
    ! [X25: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('85',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['70','86'])).

thf('88',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['4','87'])).

thf('89',plain,(
    $false ),
    inference(simplify,[status(thm)],['88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Udgrrg3EX3
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 388 iterations in 0.186s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.64  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(t26_wellord1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ C ) =>
% 0.46/0.64       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.46/0.64         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k2_wellord1 @ X40 @ X41) @ X42)
% 0.46/0.64            = (k2_wellord1 @ X40 @ (k3_xboole_0 @ X41 @ X42)))
% 0.46/0.64          | ~ (v1_relat_1 @ X40))),
% 0.46/0.64      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.46/0.64  thf(t29_wellord1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ C ) =>
% 0.46/0.64       ( ( r1_tarski @ A @ B ) =>
% 0.46/0.64         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.46/0.64           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ( v1_relat_1 @ C ) =>
% 0.46/0.64          ( ( r1_tarski @ A @ B ) =>
% 0.46/0.64            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.46/0.64              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.46/0.64         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      ((((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.46/0.64          != (k2_wellord1 @ sk_C @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('3', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.46/0.64         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.64      inference('simplify', [status(thm)], ['5'])).
% 0.46/0.64  thf(t125_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.46/0.64         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.46/0.64          | ((k8_relat_1 @ X20 @ X19) = (X19))
% 0.46/0.64          | ~ (v1_relat_1 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf(t17_wellord1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X38 : $i, X39 : $i]:
% 0.46/0.64         (((k2_wellord1 @ X39 @ X38)
% 0.46/0.64            = (k7_relat_1 @ (k8_relat_1 @ X38 @ X39) @ X38))
% 0.46/0.64          | ~ (v1_relat_1 @ X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k2_wellord1 @ X0 @ (k2_relat_1 @ X0))
% 0.46/0.64            = (k7_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ((k2_wellord1 @ X0 @ (k2_relat_1 @ X0))
% 0.46/0.64              = (k7_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.64  thf('12', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t71_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.64       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.64  thf('13', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X19 : $i, X20 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.46/0.64          | ((k8_relat_1 @ X20 @ X19) = (X19))
% 0.46/0.64          | ~ (v1_relat_1 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.64          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.64  thf(fc3_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.46/0.64       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.46/0.64  thf('16', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.64          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (((k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)) = (k6_relat_1 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['12', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X38 : $i, X39 : $i]:
% 0.46/0.64         (((k2_wellord1 @ X39 @ X38)
% 0.46/0.64            = (k7_relat_1 @ (k8_relat_1 @ X38 @ X39) @ X38))
% 0.46/0.64          | ~ (v1_relat_1 @ X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      ((((k2_wellord1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.46/0.64          = (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.46/0.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['18', '19'])).
% 0.46/0.64  thf('21', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('24', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X38 : $i, X39 : $i]:
% 0.46/0.64         (((k2_wellord1 @ X39 @ X38)
% 0.46/0.64            = (k7_relat_1 @ (k8_relat_1 @ X38 @ X39) @ X38))
% 0.46/0.64          | ~ (v1_relat_1 @ X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k6_relat_1 @ X0) @ X0)
% 0.46/0.64            = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf(t98_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X31 : $i]:
% 0.46/0.64         (((k7_relat_1 @ X31 @ (k1_relat_1 @ X31)) = (X31))
% 0.46/0.64          | ~ (v1_relat_1 @ X31))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.64  thf('31', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '32', '33'])).
% 0.46/0.64  thf('35', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X38 : $i, X39 : $i]:
% 0.46/0.64         (((k2_wellord1 @ X39 @ X38)
% 0.46/0.64            = (k7_relat_1 @ (k8_relat_1 @ X38 @ X39) @ X38))
% 0.46/0.64          | ~ (v1_relat_1 @ X39))),
% 0.46/0.64      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.46/0.64  thf(t87_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X27 : $i, X28 : $i]:
% 0.46/0.64         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X27 @ X28)) @ X28)
% 0.46/0.64          | ~ (v1_relat_1 @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['36', '37'])).
% 0.46/0.64  thf(dt_k8_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k8_relat_1 @ X17 @ X18)) | ~ (v1_relat_1 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X1)
% 0.46/0.64          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf(t1_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.64       ( r1_tarski @ A @ C ) ))).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.64         (~ (r1_tarski @ X3 @ X4)
% 0.46/0.64          | ~ (r1_tarski @ X4 @ X5)
% 0.46/0.64          | (r1_tarski @ X3 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X1)
% 0.46/0.64          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.46/0.64          | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['35', '42'])).
% 0.46/0.64  thf(t97_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.46/0.64         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.46/0.64          | ((k7_relat_1 @ X29 @ X30) = (X29))
% 0.46/0.64          | ~ (v1_relat_1 @ X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.46/0.64          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.46/0.64              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf(dt_k2_wellord1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X36 : $i, X37 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X36) | (v1_relat_1 @ (k2_wellord1 @ X36 @ X37)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.46/0.64            = (k2_wellord1 @ X0 @ sk_A))
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.46/0.64          = (k2_wellord1 @ (k6_relat_1 @ sk_A) @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['34', '47'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '32', '33'])).
% 0.46/0.64  thf('50', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.46/0.64  thf('52', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (((k2_wellord1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['20', '51', '52'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k2_wellord1 @ X40 @ X41) @ X42)
% 0.46/0.64            = (k2_wellord1 @ X40 @ (k3_xboole_0 @ X41 @ X42)))
% 0.46/0.64          | ~ (v1_relat_1 @ X40))),
% 0.46/0.64      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)
% 0.46/0.64            = (k2_wellord1 @ (k6_relat_1 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['53', '54'])).
% 0.46/0.64  thf('56', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)
% 0.46/0.64           = (k2_wellord1 @ (k6_relat_1 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X1)
% 0.46/0.64          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r1_tarski @ 
% 0.46/0.64           (k1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)) @ 
% 0.46/0.64           (k3_xboole_0 @ sk_B @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (r1_tarski @ 
% 0.46/0.64          (k1_relat_1 @ (k2_wellord1 @ (k6_relat_1 @ sk_A) @ X0)) @ 
% 0.46/0.64          (k3_xboole_0 @ sk_B @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (((r1_tarski @ 
% 0.46/0.64         (k1_relat_1 @ 
% 0.46/0.64          (k7_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.46/0.64           (k2_relat_1 @ (k6_relat_1 @ sk_A)))) @ 
% 0.46/0.64         (k3_xboole_0 @ sk_B @ (k2_relat_1 @ (k6_relat_1 @ sk_A))))
% 0.46/0.64        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['11', '61'])).
% 0.46/0.64  thf('63', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('65', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf('66', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf('67', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('68', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63', '64', '65', '66', '67'])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X0 : $i, X2 : $i]:
% 0.46/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)
% 0.46/0.64        | ((k3_xboole_0 @ sk_B @ sk_A) = (sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      (![X0 : $i]: ((k2_wellord1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '32', '33'])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k2_wellord1 @ X40 @ X41) @ X42)
% 0.46/0.64            = (k2_wellord1 @ X40 @ (k3_xboole_0 @ X41 @ X42)))
% 0.46/0.64          | ~ (v1_relat_1 @ X40))),
% 0.46/0.64      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.46/0.64  thf(t27_wellord1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ C ) =>
% 0.46/0.64       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.46/0.64         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k2_wellord1 @ X43 @ X45) @ X44)
% 0.46/0.64            = (k2_wellord1 @ (k2_wellord1 @ X43 @ X44) @ X45))
% 0.46/0.64          | ~ (v1_relat_1 @ X43))),
% 0.46/0.64      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.46/0.64         (((k2_wellord1 @ (k2_wellord1 @ X43 @ X45) @ X44)
% 0.46/0.64            = (k2_wellord1 @ (k2_wellord1 @ X43 @ X44) @ X45))
% 0.46/0.64          | ~ (v1_relat_1 @ X43))),
% 0.46/0.64      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X1)
% 0.46/0.64          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.46/0.64      inference('clc', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r1_tarski @ 
% 0.46/0.64           (k1_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)) @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X2)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_wellord1 @ X2 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['74', '75'])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      (![X36 : $i, X37 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X36) | (v1_relat_1 @ (k2_wellord1 @ X36 @ X37)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X2)
% 0.46/0.64          | (r1_tarski @ 
% 0.46/0.64             (k1_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)) @ X1))),
% 0.46/0.64      inference('clc', [status(thm)], ['76', '77'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r1_tarski @ 
% 0.46/0.64           (k1_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)) @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X2)
% 0.46/0.64          | ~ (v1_relat_1 @ X2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['73', '78'])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X2)
% 0.46/0.64          | (r1_tarski @ 
% 0.46/0.64             (k1_relat_1 @ (k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)) @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['79'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r1_tarski @ 
% 0.46/0.64           (k1_relat_1 @ (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X2)
% 0.46/0.64          | ~ (v1_relat_1 @ X2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['72', '80'])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X2)
% 0.46/0.64          | (r1_tarski @ 
% 0.46/0.64             (k1_relat_1 @ (k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['81'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.46/0.64           X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['71', '82'])).
% 0.46/0.64  thf('84', plain, (![X25 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.46/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.64  thf('85', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.46/0.64  thf('86', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.46/0.64      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.46/0.64  thf('87', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['70', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '87'])).
% 0.46/0.64  thf('89', plain, ($false), inference('simplify', [status(thm)], ['88'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
