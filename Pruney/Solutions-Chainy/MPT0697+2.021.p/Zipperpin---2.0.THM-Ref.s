%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aI5lIfBAAg

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:39 EST 2020

% Result     : Theorem 32.54s
% Output     : Refutation 32.54s
% Verified   : 
% Statistics : Number of formulae       :  977 (421805 expanded)
%              Number of leaves         :   44 (129829 expanded)
%              Depth                    :   43
%              Number of atoms          : 9323 (3998944 expanded)
%              Number of equality atoms :  585 (111285 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t152_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( v2_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X51 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t99_funct_1])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ sk_B )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('7',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X1 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('24',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) @ X0 )
      = ( k7_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['26','29','30'])).

thf(t84_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( v2_funct_1 @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('32',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( v2_funct_1 @ ( k7_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t84_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('35',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('36',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) )
        = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ sk_B )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) )
      = ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( v1_funct_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('59',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('60',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ X30 )
        = ( k4_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('68',plain,(
    ! [X25: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X25 ) )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('69',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X21 ) @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('71',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ X30 )
        = ( k4_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_funct_1 @ sk_B )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('81',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65','66','89'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) @ X0 )
      = ( k7_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['26','29','30'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('94',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
        = ( k9_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf(t126_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('96',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X36 @ X37 ) @ X38 )
        = ( k3_xboole_0 @ X36 @ ( k9_relat_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t126_funct_1])).

thf('97',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('98',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X36 @ X37 ) @ X38 )
        = ( k3_xboole_0 @ X36 @ ( k9_relat_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t126_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('99',plain,(
    ! [X24: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('100',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('105',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('108',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('110',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X43 @ X42 ) @ X44 )
        = ( k3_xboole_0 @ X42 @ ( k10_relat_1 @ X43 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('113',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('114',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k10_relat_1 @ X17 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('121',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('124',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('127',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119','125','126','127'])).

thf('129',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k10_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['111','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119','125','126','127'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['98','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) @ ( k9_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','134'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('140',plain,(
    ! [X25: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X25 ) )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('141',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X21 ) @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['139','144'])).

thf('146',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('147',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('148',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ X30 )
        = ( k4_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('152',plain,(
    ! [X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('153',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('159',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('160',plain,(
    ! [X31: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('161',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('167',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('168',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','157','158','165','166','167','168','169','170'])).

thf('172',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('173',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('175',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('176',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('177',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('182',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( v2_funct_1 @ ( k7_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t84_funct_1])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['181','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('188',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('189',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','157','158','165','166','167','168','169','170'])).

thf('190',plain,(
    ! [X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('191',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('193',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('194',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('195',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','157','158','165','166','167','168','169','170'])).

thf('197',plain,(
    ! [X31: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('198',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('200',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('201',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('202',plain,(
    v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['186','187','188','195','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('210',plain,(
    ! [X31: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('211',plain,(
    ! [X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['210','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['209','216'])).

thf('218',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('219',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('220',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) ) )
    = ( k4_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','157','158','165','166','167','168','169','170'])).

thf('222',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','157','158','165','166','167','168','169','170'])).

thf('223',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('225',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('227',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('228',plain,(
    v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('229',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['225','226','227','228'])).

thf('230',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['208','231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['203','233'])).

thf('235',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('238',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X51 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t99_funct_1])).

thf('239',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('240',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('241',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ X30 )
        = ( k4_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['239','242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['238','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['237','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ sk_B )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['249','250'])).

thf('252',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('253',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('257',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('258',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('259',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['256','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('262',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('263',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['260','261','262','263'])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['248','264'])).

thf('266',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('268',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['265','266','267','268','269','270'])).

thf('272',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X51 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t99_funct_1])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['271','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('275',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['274','275'])).

thf('277',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('278',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('279',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('281',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('282',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['280','281'])).

thf('283',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('284',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('285',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('287',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( v2_funct_1 @ ( k7_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t84_funct_1])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['286','287'])).

thf('289',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('290',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('291',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('292',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('293',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['273','279','285','292'])).

thf('294',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('295',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('296',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k1_relat_1 @ X47 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('297',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['294','297'])).

thf('299',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['298'])).

thf('300',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['293','299'])).

thf('301',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('302',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('303',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('304',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['303','304'])).

thf('306',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('308',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k2_relat_1 @ ( k2_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['300','301','302','307'])).

thf('309',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['265','266','267','268','269','270'])).

thf('310',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('311',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
        = ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['309','310'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['265','266','267','268','269','270'])).

thf('313',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('314',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('315',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('316',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['311','312','313','314','315'])).

thf('317',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['308','316'])).

thf('318',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('319',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['318','319'])).

thf('321',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['225','226','227','228'])).

thf('322',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['320','321'])).

thf('323',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('324',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('325',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['323','324'])).

thf('326',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('327',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('328',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['325','326','327'])).

thf('329',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('330',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('331',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['329','330'])).

thf('332',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('333',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('334',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['331','332','333'])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('336',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( v2_funct_1 @ ( k7_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t84_funct_1])).

thf('337',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['335','336'])).

thf('338',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('339',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('340',plain,(
    v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('341',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['337','338','339','340'])).

thf('342',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['236','317','322','328','334','341'])).

thf('343',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X43 @ X42 ) @ X44 )
        = ( k3_xboole_0 @ X42 @ ( k10_relat_1 @ X43 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('344',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('345',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('346',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('347',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('348',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('349',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['347','348'])).

thf('350',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['349'])).

thf('351',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['346','350'])).

thf('352',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['351'])).

thf('353',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['345','352'])).

thf('354',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['344','353'])).

thf('355',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['354'])).

thf('356',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['343','355'])).

thf('357',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['356'])).

thf('358',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['342','357'])).

thf('359',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('360',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('361',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['359','360'])).

thf('362',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('363',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['361','362'])).

thf('364',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['225','226','227','228'])).

thf('365',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('366',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['364','365'])).

thf('367',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('368',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['363','366','367'])).

thf('369',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['364','365'])).

thf('370',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k10_relat_1 @ X17 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('371',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119','125','126','127'])).

thf('372',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['370','371'])).

thf('373',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('374',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['372','373'])).

thf('375',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['369','374'])).

thf('376',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('377',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('378',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['376','377'])).

thf('379',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('380',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k1_relat_1 @ X47 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('381',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['379','380'])).

thf('382',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('383',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','157','158','165','166','167','168','169','170'])).

thf('384',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('385',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['381','382','383','384'])).

thf('386',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('387',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('388',plain,(
    v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('389',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['378','385','386','387','388'])).

thf('390',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('391',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('392',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['390','391'])).

thf('393',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('394',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('395',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['392','393','394','395'])).

thf('397',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['389','396'])).

thf('398',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['225','226','227','228'])).

thf('399',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['375','397','398'])).

thf('400',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['363','366','367'])).

thf('401',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 )
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['399','400'])).

thf('402',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('403',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('404',plain,(
    ! [X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('405',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['403','404'])).

thf('406',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['402','405'])).

thf('407',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('408',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('409',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('410',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('411',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('412',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('413',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('414',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('415',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('416',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['406','407','408','409','410','411','412','413','414','415'])).

thf('417',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('418',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('419',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( v2_funct_1 @ ( k8_relat_1 @ X51 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t99_funct_1])).

thf('420',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('421',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('422',plain,(
    ! [X31: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('423',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['421','422'])).

thf('424',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['420','423'])).

thf('425',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['424'])).

thf('426',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['419','425'])).

thf('427',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['426'])).

thf('428',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['418','427'])).

thf('429',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['428'])).

thf('430',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['417','429'])).

thf('431',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['430'])).

thf('432',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k1_relat_1 @ X47 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('433',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['431','432'])).

thf('434',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['416','433'])).

thf('435',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('436',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('437',plain,(
    ! [X31: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('438',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['436','437'])).

thf('439',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ( v2_funct_1 @ ( k4_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['435','438'])).

thf('440',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('441',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('442',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('443',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('444',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('445',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('446',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('447',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('448',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('449',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['439','440','441','442','443','444','445','446','447','448'])).

thf('450',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('451',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('452',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['450','451'])).

thf('453',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('454',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('455',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('456',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('457',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['452','453','454','455','456'])).

thf('458',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('459',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
        = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['457','458'])).

thf('460',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('461',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('462',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['460','461'])).

thf('463',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('464',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['462','463'])).

thf('465',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('466',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('467',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('468',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['459','464','465','466','467'])).

thf('469',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('470',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('471',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('472',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k2_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['434','449','468','469','470','471'])).

thf('473',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['406','407','408','409','410','411','412','413','414','415'])).

thf('474',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['430'])).

thf('475',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ X30 )
        = ( k4_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('476',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['474','475'])).

thf('477',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) )
      | ( ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) )
        = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['473','476'])).

thf('478',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['439','440','441','442','443','444','445','446','447','448'])).

thf('479',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('480',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('481',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('482',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['477','478','479','480','481'])).

thf('483',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['472','482'])).

thf('484',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('485',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('486',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['484','485'])).

thf('487',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('488',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['486','487'])).

thf('489',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['359','360'])).

thf('490',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('491',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['488','489','490'])).

thf('492',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['483','491'])).

thf('493',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['363','366','367'])).

thf('494',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('495',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['493','494'])).

thf('496',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['225','226','227','228'])).

thf('497',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['495','496'])).

thf('498',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['492','497'])).

thf('499',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['265','266','267','268','269','270'])).

thf(t128_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) )
        = ( k8_relat_1 @ A @ B ) ) ) )).

thf('500',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k8_relat_1 @ X10 @ ( k8_relat_1 @ X10 @ X11 ) )
        = ( k8_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t128_relat_1])).

thf('501',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
        = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['499','500'])).

thf('502',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['265','266','267','268','269','270'])).

thf('503',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('504',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['501','502','503'])).

thf('505',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['298'])).

thf('506',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['504','505'])).

thf('507',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['273','279','285','292'])).

thf('508',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['265','266','267','268','269','270'])).

thf('509',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('510',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['508','509'])).

thf('511',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('512',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('513',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['510','511','512'])).

thf('514',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['265','266','267','268','269','270'])).

thf('515',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('516',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['514','515'])).

thf('517',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('518',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('519',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['516','517','518'])).

thf('520',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['501','502','503'])).

thf('521',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('522',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['501','502','503'])).

thf('523',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['311','312','313','314','315'])).

thf('524',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('525',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('526',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['524','525'])).

thf('527',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('528',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['526','527'])).

thf('529',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['506','507','513','519','520','521','522','523','528'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('530',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k9_relat_1 @ X46 @ ( k10_relat_1 @ X46 @ X45 ) )
        = ( k3_xboole_0 @ X45 @ ( k9_relat_1 @ X46 @ ( k1_relat_1 @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('531',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['529','530'])).

thf('532',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['506','507','513','519','520','521','522','523','528'])).

thf('533',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','157','158','165','166','167','168','169','170'])).

thf('534',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('535',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['533','534'])).

thf('536',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('537',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k1_relat_1 @ X47 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('538',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['536','537'])).

thf('539',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('540',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('541',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('542',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['538','539','540','541'])).

thf('543',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('544',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('545',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('546',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['535','542','543','544','545'])).

thf('547',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['538','539','540','541'])).

thf('548',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('549',plain,
    ( ( ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_B ) )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['547','548'])).

thf('550',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('551',plain,
    ( ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['549','550'])).

thf('552',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['349'])).

thf('553',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['551','552'])).

thf('554',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['392','393','394','395'])).

thf('555',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('556',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['553','554','555'])).

thf('557',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('558',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('559',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['531','532','546','556','557','558'])).

thf('560',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['452','453','454','455','456'])).

thf('561',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['488','489','490'])).

thf('562',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['560','561'])).

thf('563',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('564',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
        = ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['562','563'])).

thf('565',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['462','463'])).

thf('566',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['359','360'])).

thf('567',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('568',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['566','567'])).

thf('569',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('570',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['568','569'])).

thf('571',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('572',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('573',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('574',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['564','565','570','571','572','573'])).

thf('575',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['559','574'])).

thf('576',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('577',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('578',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) @ X6 )
        = ( k7_relat_1 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('579',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['577','578'])).

thf('580',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('581',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('582',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['579','580','581'])).

thf('583',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['576','582'])).

thf('584',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('585',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['583','584'])).

thf('586',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['349'])).

thf('587',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['585','586'])).

thf('588',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('589',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119','125','126','127'])).

thf('590',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('591',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['587','588','589','590'])).

thf('592',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['225','226','227','228'])).

thf('593',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('594',plain,(
    ! [X31: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X31 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('595',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['593','594'])).

thf('596',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('597',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('598',plain,(
    v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('599',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['595','596','597','598'])).

thf('600',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['358','368','401','498','575','591','592','599'])).

thf('601',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['583','584'])).

thf('602',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('603',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('604',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['602','603'])).

thf('605',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('606',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['604','605'])).

thf('607',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['601','606'])).

thf('608',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['604','605'])).

thf('609',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['607','608'])).

thf('610',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['600','609'])).

thf('611',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['358','368','401','498','575','591','592','599'])).

thf('612',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['559','574'])).

thf('613',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('614',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X43 @ X42 ) @ X44 )
        = ( k3_xboole_0 @ X42 @ ( k10_relat_1 @ X43 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('615',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['613','614'])).

thf('616',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('617',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['615','616'])).

thf('618',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['564','565','570','571','572','573'])).

thf('619',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['617','618'])).

thf('620',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k9_relat_1 @ X46 @ ( k10_relat_1 @ X46 @ X45 ) )
        = ( k3_xboole_0 @ X45 @ ( k9_relat_1 @ X46 @ ( k1_relat_1 @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('621',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('622',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['620','621'])).

thf('623',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ ( k1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['619','622'])).

thf('624',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('625',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['535','542','543','544','545'])).

thf('626',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k10_relat_1 @ X17 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('627',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['625','626'])).

thf('628',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('629',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['627','628'])).

thf('630',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['624','629'])).

thf('631',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119','125','126','127'])).

thf('632',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('633',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('634',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['630','631','632','633'])).

thf('635',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('636',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['634','635'])).

thf('637',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('638',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) @ X6 )
        = ( k7_relat_1 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('639',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ X1 )
        = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['637','638'])).

thf('640',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','179','180'])).

thf('641',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('642',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ X1 )
      = ( k4_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['639','640','641'])).

thf('643',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('644',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['642','643'])).

thf('645',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['308','316'])).

thf('646',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['325','326','327'])).

thf('647',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['644','645','646'])).

thf('648',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('649',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['538','539','540','541'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('650',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ X14 @ ( k3_xboole_0 @ ( k2_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('651',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['649','650'])).

thf('652',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('653',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['651','652'])).

thf('654',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['392','393','394','395'])).

thf('655',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k9_relat_1 @ X46 @ ( k10_relat_1 @ X46 @ X45 ) )
        = ( k3_xboole_0 @ X45 @ ( k9_relat_1 @ X46 @ ( k1_relat_1 @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('656',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['654','655'])).

thf('657',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('658',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('659',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['656','657','658'])).

thf('660',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('661',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['462','463'])).

thf('662',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['660','661'])).

thf('663',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['538','539','540','541'])).

thf('664',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('665',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['662','663','664'])).

thf('666',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['659','665'])).

thf('667',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['587','588','589','590'])).

thf('668',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['644','645','646'])).

thf('669',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['587','588','589','590'])).

thf('670',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['553','554','555'])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('671',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k3_xboole_0 @ X40 @ X41 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X39 @ X40 ) @ ( k10_relat_1 @ X39 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('672',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['670','671'])).

thf('673',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('674',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('675',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      = ( k3_xboole_0 @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['672','673','674'])).

thf('676',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['634','635'])).

thf('677',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k4_relat_1 @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['644','645','646'])).

thf('678',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('679',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['651','652'])).

thf('680',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['331','332','333'])).

thf('681',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['325','326','327'])).

thf('682',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['623','636','647','648','653','666','667','668','669','675','676','677','678','679','680','681'])).

thf('683',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['612','682'])).

thf('684',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['559','574'])).

thf('685',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['683','684'])).

thf('686',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['607','608'])).

thf('687',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['685','686'])).

thf('688',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('689',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['604','605'])).

thf('690',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['688','689'])).

thf('691',plain,(
    ! [X24: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('692',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['690','691'])).

thf('693',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['687','692'])).

thf('694',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ ( k2_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['611','693'])).

thf('695',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['583','584'])).

thf('696',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('697',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('698',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['696','697'])).

thf('699',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('700',plain,(
    ! [X25: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X25 ) )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('701',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('702',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k8_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('703',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['701','702'])).

thf('704',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('705',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('706',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['698','699','700','703','704','705'])).

thf('707',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['695','706'])).

thf('708',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['698','699','700','703','704','705'])).

thf('709',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['707','708'])).

thf('710',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['604','605'])).

thf('711',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['709','710'])).

thf('712',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['604','605'])).

thf('713',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['711','712'])).

thf('714',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['694','713'])).

thf('715',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['610','714'])).

thf('716',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_B @ X0 ) @ ( k2_relat_1 @ sk_B ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ ( k9_relat_1 @ sk_B @ X0 ) ) @ ( k9_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['138','715'])).

thf('717',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['358','368','401','498','575','591','592','599'])).

thf('718',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['690','691'])).

thf('719',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('720',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('721',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) )
      = ( k9_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['716','717','718','719','720'])).

thf('722',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) @ X0 )
        = ( k9_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['96','721'])).

thf('723',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('724',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('725',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) @ X0 )
      = ( k9_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['722','723','724'])).

thf('726',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('727',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k9_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['95','725','726'])).

thf('728',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('729',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) @ X0 )
      = ( k7_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['26','29','30'])).

thf('730',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('731',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['729','730'])).

thf('732',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('733',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('734',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['731','732','733'])).

thf('735',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) @ X0 )
      = ( k7_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['26','29','30'])).

thf('736',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('737',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ ( k2_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['735','736'])).

thf('738',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('739',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('740',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['737','738','739'])).

thf('741',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('742',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['92','727','728','734','740','741'])).

thf('743',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k9_relat_1 @ X46 @ ( k10_relat_1 @ X46 @ X45 ) )
        = ( k3_xboole_0 @ X45 @ ( k9_relat_1 @ X46 @ ( k1_relat_1 @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('744',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('745',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['743','744'])).

thf('746',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) ) @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['742','745'])).

thf('747',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('748',plain,(
    ! [X9: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X9 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('749',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ sk_B )
      = ( k5_relat_1 @ sk_B @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('750',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('751',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
        = ( k10_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['749','750'])).

thf('752',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('753',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k10_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['751','752'])).

thf('754',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['748','753'])).

thf('755',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('756',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['754','755'])).

thf('757',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k3_xboole_0 @ X40 @ X41 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X39 @ X40 ) @ ( k10_relat_1 @ X39 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('758',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['756','757'])).

thf('759',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('760',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('761',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['758','759','760'])).

thf('762',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['351'])).

thf('763',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['617','618'])).

thf('764',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
        = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['762','763'])).

thf('765',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['634','635'])).

thf('766',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['308','316'])).

thf('767',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['659','665'])).

thf('768',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['587','588','589','590'])).

thf('769',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['325','326','327'])).

thf('770',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['764','765','766','767','768','769'])).

thf('771',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['761','770'])).

thf('772',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['358','368','401','498','575','591','592','599'])).

thf('773',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ X14 @ ( k3_xboole_0 @ ( k2_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('774',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ X0 )
        = ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['772','773'])).

thf('775',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('776',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ X0 )
      = ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['774','775'])).

thf('777',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ X0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['771','776'])).

thf('778',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['764','765','766','767','768','769'])).

thf('779',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k10_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ X14 @ ( k3_xboole_0 @ ( k2_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('780',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119','125','126','127'])).

thf('781',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['779','780'])).

thf('782',plain,(
    ! [X24: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('783',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119','125','126','127'])).

thf('784',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('785',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['781','782','783','784'])).

thf('786',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['583','584'])).

thf('787',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['785','786'])).

thf('788',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['698','699','700','703','704','705'])).

thf('789',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['787','788'])).

thf('790',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['698','699','700','703','704','705'])).

thf('791',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['583','584'])).

thf('792',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['789','790','791'])).

thf('793',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['778','792'])).

thf('794',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('795',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['793','794'])).

thf('796',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      = ( k6_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['777','795'])).

thf('797',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['793','794'])).

thf('798',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('799',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['797','798'])).

thf('800',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( v2_funct_1 @ ( k7_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t84_funct_1])).

thf('801',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['799','800'])).

thf('802',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('803',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('804',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('805',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['801','802','803','804'])).

thf('806',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['796','805'])).

thf('807',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('808',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['806','807'])).

thf('809',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('810',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k4_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['808','809'])).

thf('811',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('812',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('813',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','87','88'])).

thf('814',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      = ( k8_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['810','811','812','813'])).

thf('815',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('816',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k1_relat_1 @ ( k8_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k4_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['814','815'])).

thf('817',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('818',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      = ( k6_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['777','795'])).

thf('819',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['797','798'])).

thf('820',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('821',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['819','820'])).

thf('822',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('823',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('824',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['821','822','823'])).

thf('825',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['818','824'])).

thf('826',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('827',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['825','826'])).

thf('828',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      = ( k6_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['777','795'])).

thf('829',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) )
      = ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['797','798'])).

thf('830',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('831',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['829','830'])).

thf('832',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('833',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('834',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['831','832','833'])).

thf('835',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['828','834'])).

thf('836',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('837',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['835','836'])).

thf('838',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['806','807'])).

thf('839',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['816','817','827','837','838'])).

thf('840',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
        = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['747','839'])).

thf('841',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('842',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( v2_funct_1 @ ( k7_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t84_funct_1])).

thf('843',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( v2_funct_1 @ ( k7_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t84_funct_1])).

thf('844',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('845',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['821','822','823'])).

thf('846',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['844','845'])).

thf('847',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('848',plain,(
    v1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['846','847'])).

thf('849',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_funct_1 @ X30 )
        = ( k4_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('850',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
      = ( k4_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['848','849'])).

thf('851',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('852',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k5_relat_1 @ ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['831','832','833'])).

thf('853',plain,(
    v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['851','852'])).

thf('854',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_B @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('855',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['853','854'])).

thf('856',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','87','88'])).

thf('857',plain,
    ( ( k8_relat_1 @ ( k1_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['549','550'])).

thf('858',plain,
    ( ( ( k2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
      = ( k4_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['850','855','856','857'])).

thf('859',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
      = ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['843','858'])).

thf('860',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('861',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('862',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('863',plain,
    ( ( k2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    = ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['859','860','861','862'])).

thf('864',plain,(
    ! [X47: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relat_1 @ X47 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('865',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['863','864'])).

thf('866',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['392','393','394','395'])).

thf('867',plain,(
    v1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['846','847'])).

thf('868',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['853','854'])).

thf('869',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['865','866','867','868'])).

thf('870',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['842','869'])).

thf('871',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('872',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('873',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('874',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['870','871','872','873'])).

thf('875',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['841','874'])).

thf('876',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('877',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['875','876'])).

thf('878',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k9_relat_1 @ X46 @ ( k10_relat_1 @ X46 @ X45 ) )
        = ( k3_xboole_0 @ X45 @ ( k9_relat_1 @ X46 @ ( k1_relat_1 @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('879',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['877','878'])).

thf('880',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('881',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('882',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['879','880','881'])).

thf('883',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('884',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) )
      = ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['840','882','883'])).

thf('885',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k10_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['659','665'])).

thf('886',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['884','885'])).

thf('887',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('888',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) @ X6 )
        = ( k7_relat_1 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('889',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ X1 )
        = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['887','888'])).

thf('890',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) )
      = ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['251','254','255'])).

thf('891',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('892',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ X1 )
      = ( k4_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['889','890','891'])).

thf('893',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('894',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ sk_B ) ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ sk_B ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['892','893'])).

thf('895',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['462','463'])).

thf('896',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('897',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['894','895','896'])).

thf('898',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['564','565','570','571','572','573'])).

thf('899',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['351'])).

thf('900',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k3_xboole_0 @ X40 @ X41 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X39 @ X40 ) @ ( k10_relat_1 @ X39 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('901',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['899','900'])).

thf('902',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['901'])).

thf('903',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['898','902'])).

thf('904',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['381','382','383','384'])).

thf('905',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['392','393','394','395'])).

thf('906',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['904','905'])).

thf('907',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['564','565','570','571','572','573'])).

thf('908',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['894','895','896'])).

thf('909',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['535','542','543','544','545'])).

thf('910',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['764','765','766','767','768','769'])).

thf('911',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('912',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k4_relat_1 @ sk_B ) ) ) @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['617','618'])).

thf('913',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['911','912'])).

thf('914',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_B ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','157','158','165','166','167','168','169','170'])).

thf('915',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k10_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['564','565','570','571','572','573'])).

thf('916',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['538','539','540','541'])).

thf('917',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('918',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('919',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('920',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['913','914','915','916','917','918','919'])).

thf('921',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('922',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('923',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['903','906','907','908','909','910','920','921','922'])).

thf('924',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['764','765','766','767','768','769'])).

thf('925',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['886','897','923','924'])).

thf('926',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ X0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['771','776'])).

thf('927',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_B @ X0 )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['925','926'])).

thf('928',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('929',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('930',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['746','927','928','929'])).

thf('931',plain,(
    $false ),
    inference(demod,[status(thm)],['0','930'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aI5lIfBAAg
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 32.54/32.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 32.54/32.74  % Solved by: fo/fo7.sh
% 32.54/32.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.54/32.74  % done 11593 iterations in 32.253s
% 32.54/32.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 32.54/32.74  % SZS output start Refutation
% 32.54/32.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 32.54/32.74  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 32.54/32.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 32.54/32.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 32.54/32.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 32.54/32.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 32.54/32.74  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 32.54/32.74  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 32.54/32.74  thf(sk_A_type, type, sk_A: $i).
% 32.54/32.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 32.54/32.74  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 32.54/32.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 32.54/32.74  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 32.54/32.74  thf(sk_B_type, type, sk_B: $i).
% 32.54/32.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 32.54/32.74  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 32.54/32.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 32.54/32.74  thf(t152_funct_1, conjecture,
% 32.54/32.74    (![A:$i,B:$i]:
% 32.54/32.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 32.54/32.74       ( ( v2_funct_1 @ B ) =>
% 32.54/32.74         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 32.54/32.74  thf(zf_stmt_0, negated_conjecture,
% 32.54/32.74    (~( ![A:$i,B:$i]:
% 32.54/32.74        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 32.54/32.74          ( ( v2_funct_1 @ B ) =>
% 32.54/32.74            ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )),
% 32.54/32.74    inference('cnf.neg', [status(esa)], [t152_funct_1])).
% 32.54/32.74  thf('0', plain,
% 32.54/32.74      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf(t99_funct_1, axiom,
% 32.54/32.74    (![A:$i,B:$i]:
% 32.54/32.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 32.54/32.74       ( ( v2_funct_1 @ B ) => ( v2_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ))).
% 32.54/32.74  thf('1', plain,
% 32.54/32.74      (![X50 : $i, X51 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X50)
% 32.54/32.74          | (v2_funct_1 @ (k8_relat_1 @ X51 @ X50))
% 32.54/32.74          | ~ (v1_funct_1 @ X50)
% 32.54/32.74          | ~ (v1_relat_1 @ X50))),
% 32.54/32.74      inference('cnf', [status(esa)], [t99_funct_1])).
% 32.54/32.74  thf(t126_relat_1, axiom,
% 32.54/32.74    (![A:$i]:
% 32.54/32.74     ( ( v1_relat_1 @ A ) =>
% 32.54/32.74       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 32.54/32.74  thf('2', plain,
% 32.54/32.74      (![X9 : $i]:
% 32.54/32.74         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.74      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.74  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf(t123_relat_1, axiom,
% 32.54/32.74    (![A:$i,B:$i]:
% 32.54/32.74     ( ( v1_relat_1 @ B ) =>
% 32.54/32.74       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 32.54/32.74  thf('4', plain,
% 32.54/32.74      (![X7 : $i, X8 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.74          | ~ (v1_relat_1 @ X7))),
% 32.54/32.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.74  thf('5', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ sk_B) = (k5_relat_1 @ sk_B @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['3', '4'])).
% 32.54/32.74  thf(fc9_funct_1, axiom,
% 32.54/32.74    (![A:$i,B:$i]:
% 32.54/32.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 32.54/32.74       ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) & 
% 32.54/32.74         ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ))).
% 32.54/32.74  thf('6', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('7', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('8', plain,
% 32.54/32.74      (![X9 : $i]:
% 32.54/32.74         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.74      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.74  thf('9', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('10', plain,
% 32.54/32.74      (![X7 : $i, X8 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.74          | ~ (v1_relat_1 @ X7))),
% 32.54/32.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.74  thf('11', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k5_relat_1 @ (k8_relat_1 @ X1 @ X0) @ (k6_relat_1 @ X2))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['9', '10'])).
% 32.54/32.74  thf('12', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 32.54/32.74            = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('sup+', [status(thm)], ['8', '11'])).
% 32.54/32.74  thf('13', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ((k8_relat_1 @ X1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 32.54/32.74              = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 32.54/32.74      inference('simplify', [status(thm)], ['12'])).
% 32.54/32.74  thf('14', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('15', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X1) @ X1))
% 32.54/32.74          | ~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ X1) @ X1)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['13', '14'])).
% 32.54/32.74  thf('16', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['7', '15'])).
% 32.54/32.74  thf('17', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('simplify', [status(thm)], ['16'])).
% 32.54/32.74  thf('18', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['6', '17'])).
% 32.54/32.74  thf('19', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('simplify', [status(thm)], ['18'])).
% 32.54/32.74  thf('20', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74          | ~ (v1_relat_1 @ sk_B)
% 32.54/32.74          | ~ (v1_funct_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['5', '19'])).
% 32.54/32.74  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('23', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['20', '21', '22'])).
% 32.54/32.74  thf(t94_relat_1, axiom,
% 32.54/32.74    (![A:$i,B:$i]:
% 32.54/32.74     ( ( v1_relat_1 @ B ) =>
% 32.54/32.74       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 32.54/32.74  thf('24', plain,
% 32.54/32.74      (![X28 : $i, X29 : $i]:
% 32.54/32.74         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 32.54/32.74          | ~ (v1_relat_1 @ X29))),
% 32.54/32.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 32.54/32.74  thf('25', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k8_relat_1 @ X0 @ sk_B) @ X1)
% 32.54/32.74           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['23', '24'])).
% 32.54/32.74  thf('26', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k7_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B) @ X0)
% 32.54/32.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))
% 32.54/32.74          | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['2', '25'])).
% 32.54/32.74  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('28', plain,
% 32.54/32.74      (![X28 : $i, X29 : $i]:
% 32.54/32.74         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 32.54/32.74          | ~ (v1_relat_1 @ X29))),
% 32.54/32.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 32.54/32.74  thf('29', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k7_relat_1 @ sk_B @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 32.54/32.74      inference('sup-', [status(thm)], ['27', '28'])).
% 32.54/32.74  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('31', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B) @ X0)
% 32.54/32.74           = (k7_relat_1 @ sk_B @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['26', '29', '30'])).
% 32.54/32.74  thf(t84_funct_1, axiom,
% 32.54/32.74    (![A:$i,B:$i]:
% 32.54/32.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 32.54/32.74       ( ( v2_funct_1 @ B ) => ( v2_funct_1 @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 32.54/32.74  thf('32', plain,
% 32.54/32.74      (![X48 : $i, X49 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X48)
% 32.54/32.74          | (v2_funct_1 @ (k7_relat_1 @ X48 @ X49))
% 32.54/32.74          | ~ (v1_funct_1 @ X48)
% 32.54/32.74          | ~ (v1_relat_1 @ X48))),
% 32.54/32.74      inference('cnf', [status(esa)], [t84_funct_1])).
% 32.54/32.74  thf('33', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v2_funct_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))
% 32.54/32.74          | ~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))
% 32.54/32.74          | ~ (v2_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['31', '32'])).
% 32.54/32.74  thf('34', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['20', '21', '22'])).
% 32.54/32.74  thf('35', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('36', plain,
% 32.54/32.74      (![X9 : $i]:
% 32.54/32.74         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.74      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.74  thf('37', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['20', '21', '22'])).
% 32.54/32.74  thf('38', plain,
% 32.54/32.74      (![X7 : $i, X8 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.74          | ~ (v1_relat_1 @ X7))),
% 32.54/32.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.74  thf('39', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74           = (k5_relat_1 @ (k8_relat_1 @ X0 @ sk_B) @ (k6_relat_1 @ X1)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['37', '38'])).
% 32.54/32.74  thf('40', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X0 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))
% 32.54/32.74            = (k5_relat_1 @ sk_B @ (k6_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['36', '39'])).
% 32.54/32.74  thf('41', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ sk_B) = (k5_relat_1 @ sk_B @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['3', '4'])).
% 32.54/32.74  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('43', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))
% 32.54/32.74           = (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['40', '41', '42'])).
% 32.54/32.74  thf('44', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('45', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))
% 32.54/32.74          | ~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['43', '44'])).
% 32.54/32.74  thf('46', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['20', '21', '22'])).
% 32.54/32.74  thf('47', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74          | ~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['45', '46'])).
% 32.54/32.74  thf('48', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ sk_B)
% 32.54/32.74          | ~ (v1_funct_1 @ sk_B)
% 32.54/32.74          | (v1_funct_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['35', '47'])).
% 32.54/32.74  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('51', plain, (![X0 : $i]: (v1_funct_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['48', '49', '50'])).
% 32.54/32.74  thf('52', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v2_funct_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74          | ~ (v2_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['33', '34', '51'])).
% 32.54/32.74  thf('53', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ sk_B)
% 32.54/32.74          | ~ (v1_funct_1 @ sk_B)
% 32.54/32.74          | ~ (v2_funct_1 @ sk_B)
% 32.54/32.74          | (v2_funct_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['1', '52'])).
% 32.54/32.74  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('56', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('57', plain, (![X0 : $i]: (v2_funct_1 @ (k7_relat_1 @ sk_B @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 32.54/32.74  thf(fc8_funct_1, axiom,
% 32.54/32.74    (![A:$i,B:$i]:
% 32.54/32.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.54/32.74       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 32.54/32.74         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 32.54/32.74  thf('58', plain,
% 32.54/32.74      (![X32 : $i, X33 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X32)
% 32.54/32.74          | ~ (v1_relat_1 @ X32)
% 32.54/32.74          | (v1_funct_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.74  thf('59', plain,
% 32.54/32.74      (![X32 : $i, X33 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X32)
% 32.54/32.74          | ~ (v1_relat_1 @ X32)
% 32.54/32.74          | (v1_relat_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.74  thf(d9_funct_1, axiom,
% 32.54/32.74    (![A:$i]:
% 32.54/32.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.54/32.74       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 32.54/32.74  thf('60', plain,
% 32.54/32.74      (![X30 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X30)
% 32.54/32.74          | ((k2_funct_1 @ X30) = (k4_relat_1 @ X30))
% 32.54/32.74          | ~ (v1_funct_1 @ X30)
% 32.54/32.74          | ~ (v1_relat_1 @ X30))),
% 32.54/32.74      inference('cnf', [status(esa)], [d9_funct_1])).
% 32.54/32.74  thf('61', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74          | ((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['59', '60'])).
% 32.54/32.74  thf('62', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74          | ((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('sup-', [status(thm)], ['58', '61'])).
% 32.54/32.74  thf('63', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('simplify', [status(thm)], ['62'])).
% 32.54/32.74  thf('64', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ sk_B)
% 32.54/32.74          | ~ (v1_funct_1 @ sk_B)
% 32.54/32.74          | ((k2_funct_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k7_relat_1 @ sk_B @ X0))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['57', '63'])).
% 32.54/32.74  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('66', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('67', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k7_relat_1 @ sk_B @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 32.54/32.74      inference('sup-', [status(thm)], ['27', '28'])).
% 32.54/32.74  thf(t72_relat_1, axiom,
% 32.54/32.74    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 32.54/32.74  thf('68', plain,
% 32.54/32.74      (![X25 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X25)) = (k6_relat_1 @ X25))),
% 32.54/32.74      inference('cnf', [status(esa)], [t72_relat_1])).
% 32.54/32.74  thf(t54_relat_1, axiom,
% 32.54/32.74    (![A:$i]:
% 32.54/32.74     ( ( v1_relat_1 @ A ) =>
% 32.54/32.74       ( ![B:$i]:
% 32.54/32.74         ( ( v1_relat_1 @ B ) =>
% 32.54/32.74           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 32.54/32.74             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 32.54/32.74  thf('69', plain,
% 32.54/32.74      (![X21 : $i, X22 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X21)
% 32.54/32.74          | ((k4_relat_1 @ (k5_relat_1 @ X22 @ X21))
% 32.54/32.74              = (k5_relat_1 @ (k4_relat_1 @ X21) @ (k4_relat_1 @ X22)))
% 32.54/32.74          | ~ (v1_relat_1 @ X22))),
% 32.54/32.74      inference('cnf', [status(esa)], [t54_relat_1])).
% 32.54/32.74  thf('70', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 32.54/32.74            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('sup+', [status(thm)], ['68', '69'])).
% 32.54/32.74  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 32.54/32.74  thf('71', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('72', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 32.54/32.74            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['70', '71'])).
% 32.54/32.74  thf('73', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74            = (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['67', '72'])).
% 32.54/32.74  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('75', plain,
% 32.54/32.74      (![X30 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X30)
% 32.54/32.74          | ((k2_funct_1 @ X30) = (k4_relat_1 @ X30))
% 32.54/32.74          | ~ (v1_funct_1 @ X30)
% 32.54/32.74          | ~ (v1_relat_1 @ X30))),
% 32.54/32.74      inference('cnf', [status(esa)], [d9_funct_1])).
% 32.54/32.74  thf('76', plain,
% 32.54/32.74      ((~ (v1_funct_1 @ sk_B)
% 32.54/32.74        | ((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v2_funct_1 @ sk_B))),
% 32.54/32.74      inference('sup-', [status(thm)], ['74', '75'])).
% 32.54/32.74  thf('77', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('78', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('79', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.74  thf(fc6_funct_1, axiom,
% 32.54/32.74    (![A:$i]:
% 32.54/32.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 32.54/32.74       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 32.54/32.74         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 32.54/32.74         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 32.54/32.74  thf('80', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('81', plain,
% 32.54/32.74      (((v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v1_relat_1 @ sk_B)
% 32.54/32.74        | ~ (v1_funct_1 @ sk_B)
% 32.54/32.74        | ~ (v2_funct_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['79', '80'])).
% 32.54/32.74  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('84', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('85', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('86', plain,
% 32.54/32.74      (![X7 : $i, X8 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.74          | ~ (v1_relat_1 @ X7))),
% 32.54/32.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.74  thf('87', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))
% 32.54/32.74           = (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['85', '86'])).
% 32.54/32.74  thf('88', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('89', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['73', '87', '88'])).
% 32.54/32.74  thf('90', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k2_funct_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['64', '65', '66', '89'])).
% 32.54/32.74  thf(t55_funct_1, axiom,
% 32.54/32.74    (![A:$i]:
% 32.54/32.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.54/32.74       ( ( v2_funct_1 @ A ) =>
% 32.54/32.74         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 32.54/32.74           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 32.54/32.74  thf('91', plain,
% 32.54/32.74      (![X47 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X47)
% 32.54/32.74          | ((k2_relat_1 @ X47) = (k1_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.74          | ~ (v1_funct_1 @ X47)
% 32.54/32.74          | ~ (v1_relat_1 @ X47))),
% 32.54/32.74      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.74  thf('92', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k2_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74            = (k1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74          | ~ (v2_funct_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['90', '91'])).
% 32.54/32.74  thf('93', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B) @ X0)
% 32.54/32.74           = (k7_relat_1 @ sk_B @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['26', '29', '30'])).
% 32.54/32.74  thf(t148_relat_1, axiom,
% 32.54/32.74    (![A:$i,B:$i]:
% 32.54/32.74     ( ( v1_relat_1 @ B ) =>
% 32.54/32.74       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 32.54/32.74  thf('94', plain,
% 32.54/32.74      (![X12 : $i, X13 : $i]:
% 32.54/32.74         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.74          | ~ (v1_relat_1 @ X12))),
% 32.54/32.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.74  thf('95', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k2_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.74            = (k9_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B) @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['93', '94'])).
% 32.54/32.74  thf(t126_funct_1, axiom,
% 32.54/32.74    (![A:$i,B:$i,C:$i]:
% 32.54/32.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 32.54/32.74       ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 32.54/32.74         ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 32.54/32.74  thf('96', plain,
% 32.54/32.74      (![X36 : $i, X37 : $i, X38 : $i]:
% 32.54/32.74         (((k9_relat_1 @ (k8_relat_1 @ X36 @ X37) @ X38)
% 32.54/32.74            = (k3_xboole_0 @ X36 @ (k9_relat_1 @ X37 @ X38)))
% 32.54/32.74          | ~ (v1_funct_1 @ X37)
% 32.54/32.74          | ~ (v1_relat_1 @ X37))),
% 32.54/32.74      inference('cnf', [status(esa)], [t126_funct_1])).
% 32.54/32.74  thf('97', plain,
% 32.54/32.74      (![X9 : $i]:
% 32.54/32.74         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.74      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.74  thf('98', plain,
% 32.54/32.74      (![X36 : $i, X37 : $i, X38 : $i]:
% 32.54/32.74         (((k9_relat_1 @ (k8_relat_1 @ X36 @ X37) @ X38)
% 32.54/32.74            = (k3_xboole_0 @ X36 @ (k9_relat_1 @ X37 @ X38)))
% 32.54/32.74          | ~ (v1_funct_1 @ X37)
% 32.54/32.74          | ~ (v1_relat_1 @ X37))),
% 32.54/32.74      inference('cnf', [status(esa)], [t126_funct_1])).
% 32.54/32.74  thf(t71_relat_1, axiom,
% 32.54/32.74    (![A:$i]:
% 32.54/32.74     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 32.54/32.74       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 32.54/32.74  thf('99', plain, (![X24 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 32.54/32.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 32.54/32.74  thf('100', plain,
% 32.54/32.74      (![X9 : $i]:
% 32.54/32.74         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.74      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.74  thf('101', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['99', '100'])).
% 32.54/32.74  thf('102', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('103', plain,
% 32.54/32.74      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['101', '102'])).
% 32.54/32.74  thf('104', plain,
% 32.54/32.74      (![X7 : $i, X8 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.74          | ~ (v1_relat_1 @ X7))),
% 32.54/32.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.74  thf('105', plain,
% 32.54/32.74      (![X28 : $i, X29 : $i]:
% 32.54/32.74         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 32.54/32.74          | ~ (v1_relat_1 @ X29))),
% 32.54/32.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 32.54/32.74  thf('106', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.74            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['104', '105'])).
% 32.54/32.74  thf('107', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('108', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('109', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('demod', [status(thm)], ['106', '107', '108'])).
% 32.54/32.74  thf(t139_funct_1, axiom,
% 32.54/32.74    (![A:$i,B:$i,C:$i]:
% 32.54/32.74     ( ( v1_relat_1 @ C ) =>
% 32.54/32.74       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 32.54/32.74         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 32.54/32.74  thf('110', plain,
% 32.54/32.74      (![X42 : $i, X43 : $i, X44 : $i]:
% 32.54/32.74         (((k10_relat_1 @ (k7_relat_1 @ X43 @ X42) @ X44)
% 32.54/32.74            = (k3_xboole_0 @ X42 @ (k10_relat_1 @ X43 @ X44)))
% 32.54/32.74          | ~ (v1_relat_1 @ X43))),
% 32.54/32.74      inference('cnf', [status(esa)], [t139_funct_1])).
% 32.54/32.74  thf('111', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.54/32.74         (((k10_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 32.54/32.74            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['109', '110'])).
% 32.54/32.74  thf('112', plain,
% 32.54/32.74      (![X28 : $i, X29 : $i]:
% 32.54/32.74         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 32.54/32.74          | ~ (v1_relat_1 @ X29))),
% 32.54/32.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 32.54/32.74  thf('113', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 32.54/32.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 32.54/32.74  thf(t182_relat_1, axiom,
% 32.54/32.74    (![A:$i]:
% 32.54/32.74     ( ( v1_relat_1 @ A ) =>
% 32.54/32.74       ( ![B:$i]:
% 32.54/32.74         ( ( v1_relat_1 @ B ) =>
% 32.54/32.74           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 32.54/32.74             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 32.54/32.74  thf('114', plain,
% 32.54/32.74      (![X16 : $i, X17 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X16)
% 32.54/32.74          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 32.54/32.74              = (k10_relat_1 @ X17 @ (k1_relat_1 @ X16)))
% 32.54/32.74          | ~ (v1_relat_1 @ X17))),
% 32.54/32.74      inference('cnf', [status(esa)], [t182_relat_1])).
% 32.54/32.74  thf('115', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k10_relat_1 @ X1 @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['113', '114'])).
% 32.54/32.74  thf('116', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('117', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k10_relat_1 @ X1 @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['115', '116'])).
% 32.54/32.74  thf('118', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 32.54/32.74            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['112', '117'])).
% 32.54/32.74  thf('119', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('demod', [status(thm)], ['106', '107', '108'])).
% 32.54/32.74  thf('120', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.74           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('demod', [status(thm)], ['106', '107', '108'])).
% 32.54/32.74  thf(t90_relat_1, axiom,
% 32.54/32.74    (![A:$i,B:$i]:
% 32.54/32.74     ( ( v1_relat_1 @ B ) =>
% 32.54/32.74       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 32.54/32.74         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 32.54/32.74  thf('121', plain,
% 32.54/32.74      (![X26 : $i, X27 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k7_relat_1 @ X26 @ X27))
% 32.54/32.74            = (k3_xboole_0 @ (k1_relat_1 @ X26) @ X27))
% 32.54/32.74          | ~ (v1_relat_1 @ X26))),
% 32.54/32.74      inference('cnf', [status(esa)], [t90_relat_1])).
% 32.54/32.74  thf('122', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['120', '121'])).
% 32.54/32.74  thf('123', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 32.54/32.74      inference('cnf', [status(esa)], [t71_relat_1])).
% 32.54/32.74  thf('124', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('125', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74           = (k3_xboole_0 @ X1 @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['122', '123', '124'])).
% 32.54/32.74  thf('126', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('127', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('128', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['118', '119', '125', '126', '127'])).
% 32.54/32.74  thf('129', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('130', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.54/32.74         ((k10_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 32.54/32.74           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 32.54/32.74      inference('demod', [status(thm)], ['111', '128', '129'])).
% 32.54/32.74  thf('131', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 32.54/32.74           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['103', '130'])).
% 32.54/32.74  thf('132', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['118', '119', '125', '126', '127'])).
% 32.54/32.74  thf('133', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k3_xboole_0 @ X1 @ X0)
% 32.54/32.74           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.74      inference('demod', [status(thm)], ['131', '132'])).
% 32.54/32.74  thf('134', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.54/32.74         (((k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ 
% 32.54/32.74               (k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1))),
% 32.54/32.74      inference('sup+', [status(thm)], ['98', '133'])).
% 32.54/32.74  thf('135', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k3_xboole_0 @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 32.54/32.74            = (k3_xboole_0 @ (k9_relat_1 @ X0 @ X1) @ (k9_relat_1 @ X0 @ X1)))
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('sup+', [status(thm)], ['97', '134'])).
% 32.54/32.74  thf(idempotence_k3_xboole_0, axiom,
% 32.54/32.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 32.54/32.74  thf('136', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 32.54/32.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 32.54/32.74  thf('137', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k3_xboole_0 @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 32.54/32.74            = (k9_relat_1 @ X0 @ X1))
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['135', '136'])).
% 32.54/32.74  thf('138', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ((k3_xboole_0 @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 32.54/32.74              = (k9_relat_1 @ X0 @ X1)))),
% 32.54/32.74      inference('simplify', [status(thm)], ['137'])).
% 32.54/32.74  thf('139', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))
% 32.54/32.74           = (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['85', '86'])).
% 32.54/32.74  thf('140', plain,
% 32.54/32.74      (![X25 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X25)) = (k6_relat_1 @ X25))),
% 32.54/32.74      inference('cnf', [status(esa)], [t72_relat_1])).
% 32.54/32.74  thf('141', plain,
% 32.54/32.74      (![X21 : $i, X22 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X21)
% 32.54/32.74          | ((k4_relat_1 @ (k5_relat_1 @ X22 @ X21))
% 32.54/32.74              = (k5_relat_1 @ (k4_relat_1 @ X21) @ (k4_relat_1 @ X22)))
% 32.54/32.74          | ~ (v1_relat_1 @ X22))),
% 32.54/32.74      inference('cnf', [status(esa)], [t54_relat_1])).
% 32.54/32.74  thf('142', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['140', '141'])).
% 32.54/32.74  thf('143', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('144', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['142', '143'])).
% 32.54/32.74  thf('145', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 32.54/32.74               (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['139', '144'])).
% 32.54/32.74  thf('146', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.74  thf('147', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('148', plain,
% 32.54/32.74      (![X30 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X30)
% 32.54/32.74          | ((k2_funct_1 @ X30) = (k4_relat_1 @ X30))
% 32.54/32.74          | ~ (v1_funct_1 @ X30)
% 32.54/32.74          | ~ (v1_relat_1 @ X30))),
% 32.54/32.74      inference('cnf', [status(esa)], [d9_funct_1])).
% 32.54/32.74  thf('149', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 32.54/32.74          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['147', '148'])).
% 32.54/32.74  thf('150', plain,
% 32.54/32.74      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 32.54/32.74        | ((k2_funct_1 @ (k2_funct_1 @ sk_B))
% 32.54/32.74            = (k4_relat_1 @ (k2_funct_1 @ sk_B)))
% 32.54/32.74        | ~ (v2_funct_1 @ sk_B)
% 32.54/32.74        | ~ (v1_funct_1 @ sk_B)
% 32.54/32.74        | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.74      inference('sup-', [status(thm)], ['146', '149'])).
% 32.54/32.74  thf('151', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.74  thf('152', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('153', plain,
% 32.54/32.74      (((v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v1_relat_1 @ sk_B)
% 32.54/32.74        | ~ (v1_funct_1 @ sk_B)
% 32.54/32.74        | ~ (v2_funct_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['151', '152'])).
% 32.54/32.74  thf('154', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('155', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('156', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('157', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('158', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.74  thf('159', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.74  thf('160', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v2_funct_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('161', plain,
% 32.54/32.74      (((v2_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v1_relat_1 @ sk_B)
% 32.54/32.74        | ~ (v1_funct_1 @ sk_B)
% 32.54/32.74        | ~ (v2_funct_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['159', '160'])).
% 32.54/32.74  thf('162', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('163', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('164', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('165', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.74  thf('166', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.74  thf('167', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.74  thf('168', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('169', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('170', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('171', plain,
% 32.54/32.74      (((k2_funct_1 @ (k4_relat_1 @ sk_B)) = (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['150', '157', '158', '165', '166', '167', '168', '169', '170'])).
% 32.54/32.74  thf('172', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('173', plain,
% 32.54/32.74      (((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['171', '172'])).
% 32.54/32.74  thf('174', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('175', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('176', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.74  thf('177', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('178', plain,
% 32.54/32.74      (![X28 : $i, X29 : $i]:
% 32.54/32.74         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 32.54/32.74          | ~ (v1_relat_1 @ X29))),
% 32.54/32.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 32.54/32.74  thf('179', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0)
% 32.54/32.74           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 32.54/32.74              (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['177', '178'])).
% 32.54/32.74  thf('180', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('181', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.74  thf('182', plain,
% 32.54/32.74      (![X48 : $i, X49 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X48)
% 32.54/32.74          | (v2_funct_1 @ (k7_relat_1 @ X48 @ X49))
% 32.54/32.74          | ~ (v1_funct_1 @ X48)
% 32.54/32.74          | ~ (v1_relat_1 @ X48))),
% 32.54/32.74      inference('cnf', [status(esa)], [t84_funct_1])).
% 32.54/32.74  thf('183', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('simplify', [status(thm)], ['62'])).
% 32.54/32.74  thf('184', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v2_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['182', '183'])).
% 32.54/32.74  thf('185', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('simplify', [status(thm)], ['184'])).
% 32.54/32.74  thf('186', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74            = (k4_relat_1 @ 
% 32.54/32.74               (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['181', '185'])).
% 32.54/32.74  thf('187', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.74  thf('188', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('189', plain,
% 32.54/32.74      (((k2_funct_1 @ (k4_relat_1 @ sk_B)) = (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['150', '157', '158', '165', '166', '167', '168', '169', '170'])).
% 32.54/32.74  thf('190', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('191', plain,
% 32.54/32.74      (((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['189', '190'])).
% 32.54/32.74  thf('192', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('193', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('194', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.74  thf('195', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 32.54/32.74  thf('196', plain,
% 32.54/32.74      (((k2_funct_1 @ (k4_relat_1 @ sk_B)) = (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['150', '157', '158', '165', '166', '167', '168', '169', '170'])).
% 32.54/32.74  thf('197', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v2_funct_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('198', plain,
% 32.54/32.74      (((v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['196', '197'])).
% 32.54/32.74  thf('199', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('200', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('201', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.74  thf('202', plain, ((v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 32.54/32.74  thf('203', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74           = (k4_relat_1 @ 
% 32.54/32.74              (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('demod', [status(thm)], ['186', '187', '188', '195', '202'])).
% 32.54/32.74  thf('204', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0)
% 32.54/32.74           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 32.54/32.74              (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['177', '178'])).
% 32.54/32.74  thf('205', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.74  thf('206', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 32.54/32.74              (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['204', '205'])).
% 32.54/32.74  thf('207', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 32.54/32.74            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['70', '71'])).
% 32.54/32.74  thf('208', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74            = (k5_relat_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.74               (k6_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['206', '207'])).
% 32.54/32.74  thf('209', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('210', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v2_funct_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('211', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('212', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 32.54/32.74          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['147', '148'])).
% 32.54/32.74  thf('213', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 32.54/32.74          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('sup-', [status(thm)], ['211', '212'])).
% 32.54/32.74  thf('214', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('simplify', [status(thm)], ['213'])).
% 32.54/32.74  thf('215', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['210', '214'])).
% 32.54/32.74  thf('216', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('simplify', [status(thm)], ['215'])).
% 32.54/32.74  thf('217', plain,
% 32.54/32.74      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ((k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74            = (k4_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['209', '216'])).
% 32.54/32.74  thf('218', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('219', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.74  thf('220', plain,
% 32.54/32.74      (((k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74         = (k4_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['217', '218', '219'])).
% 32.54/32.74  thf('221', plain,
% 32.54/32.74      (((k2_funct_1 @ (k4_relat_1 @ sk_B)) = (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['150', '157', '158', '165', '166', '167', '168', '169', '170'])).
% 32.54/32.74  thf('222', plain,
% 32.54/32.74      (((k2_funct_1 @ (k4_relat_1 @ sk_B)) = (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['150', '157', '158', '165', '166', '167', '168', '169', '170'])).
% 32.54/32.74  thf('223', plain,
% 32.54/32.74      (((k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74         = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['220', '221', '222'])).
% 32.54/32.74  thf('224', plain,
% 32.54/32.74      (![X31 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k2_funct_1 @ X31))
% 32.54/32.74          | ~ (v2_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_funct_1 @ X31)
% 32.54/32.74          | ~ (v1_relat_1 @ X31))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.74  thf('225', plain,
% 32.54/32.74      (((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['223', '224'])).
% 32.54/32.74  thf('226', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('227', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 32.54/32.74  thf('228', plain, ((v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 32.54/32.74  thf('229', plain,
% 32.54/32.74      ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['225', '226', '227', '228'])).
% 32.54/32.74  thf('230', plain,
% 32.54/32.74      (![X7 : $i, X8 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.74          | ~ (v1_relat_1 @ X7))),
% 32.54/32.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.74  thf('231', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74           = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.74              (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['229', '230'])).
% 32.54/32.74  thf('232', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('233', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74           = (k8_relat_1 @ X0 @ 
% 32.54/32.74              (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('demod', [status(thm)], ['208', '231', '232'])).
% 32.54/32.74  thf('234', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74           = (k8_relat_1 @ X0 @ 
% 32.54/32.74              (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('demod', [status(thm)], ['203', '233'])).
% 32.54/32.74  thf('235', plain,
% 32.54/32.74      (![X47 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X47)
% 32.54/32.74          | ((k2_relat_1 @ X47) = (k1_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.74          | ~ (v1_funct_1 @ X47)
% 32.54/32.74          | ~ (v1_relat_1 @ X47))),
% 32.54/32.74      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.74  thf('236', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74            = (k1_relat_1 @ 
% 32.54/32.74               (k8_relat_1 @ X0 @ 
% 32.54/32.74                (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))
% 32.54/32.74          | ~ (v1_relat_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74          | ~ (v1_funct_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74          | ~ (v2_funct_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['234', '235'])).
% 32.54/32.74  thf('237', plain,
% 32.54/32.74      (![X9 : $i]:
% 32.54/32.74         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.74      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.74  thf('238', plain,
% 32.54/32.74      (![X50 : $i, X51 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X50)
% 32.54/32.74          | (v2_funct_1 @ (k8_relat_1 @ X51 @ X50))
% 32.54/32.74          | ~ (v1_funct_1 @ X50)
% 32.54/32.74          | ~ (v1_relat_1 @ X50))),
% 32.54/32.74      inference('cnf', [status(esa)], [t99_funct_1])).
% 32.54/32.74  thf('239', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('240', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('241', plain,
% 32.54/32.74      (![X30 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X30)
% 32.54/32.74          | ((k2_funct_1 @ X30) = (k4_relat_1 @ X30))
% 32.54/32.74          | ~ (v1_funct_1 @ X30)
% 32.54/32.74          | ~ (v1_relat_1 @ X30))),
% 32.54/32.74      inference('cnf', [status(esa)], [d9_funct_1])).
% 32.54/32.74  thf('242', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74          | ((k2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['240', '241'])).
% 32.54/32.74  thf('243', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74          | ((k2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('sup-', [status(thm)], ['239', '242'])).
% 32.54/32.74  thf('244', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('simplify', [status(thm)], ['243'])).
% 32.54/32.74  thf('245', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ((k2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['238', '244'])).
% 32.54/32.74  thf('246', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('simplify', [status(thm)], ['245'])).
% 32.54/32.74  thf('247', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k2_funct_1 @ X0)
% 32.54/32.74            = (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ X0))),
% 32.54/32.74      inference('sup+', [status(thm)], ['237', '246'])).
% 32.54/32.74  thf('248', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ((k2_funct_1 @ X0)
% 32.54/32.74              = (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))))),
% 32.54/32.74      inference('simplify', [status(thm)], ['247'])).
% 32.54/32.74  thf('249', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ sk_B) = (k5_relat_1 @ sk_B @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['3', '4'])).
% 32.54/32.74  thf('250', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['142', '143'])).
% 32.54/32.74  thf('251', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ sk_B)))
% 32.54/32.74          | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['249', '250'])).
% 32.54/32.74  thf('252', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('253', plain,
% 32.54/32.74      (![X28 : $i, X29 : $i]:
% 32.54/32.74         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 32.54/32.74          | ~ (v1_relat_1 @ X29))),
% 32.54/32.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 32.54/32.74  thf('254', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.74           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['252', '253'])).
% 32.54/32.74  thf('255', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('256', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.74  thf('257', plain,
% 32.54/32.74      (![X32 : $i, X33 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X32)
% 32.54/32.74          | ~ (v1_relat_1 @ X32)
% 32.54/32.74          | (v1_relat_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.74  thf('258', plain,
% 32.54/32.74      (![X7 : $i, X8 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.74          | ~ (v1_relat_1 @ X7))),
% 32.54/32.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.74  thf('259', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k6_relat_1 @ X2))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['257', '258'])).
% 32.54/32.74  thf('260', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X1 @ (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.74            = (k5_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)) @ 
% 32.54/32.74               (k6_relat_1 @ X1)))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['256', '259'])).
% 32.54/32.74  thf('261', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.74  thf('262', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('263', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('264', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.74           = (k5_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)) @ 
% 32.54/32.74              (k6_relat_1 @ X1)))),
% 32.54/32.74      inference('demod', [status(thm)], ['260', '261', '262', '263'])).
% 32.54/32.74  thf('265', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X0 @ 
% 32.54/32.74            (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.74            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k6_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ sk_B)
% 32.54/32.74          | ~ (v1_funct_1 @ sk_B)
% 32.54/32.74          | ~ (v2_funct_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['248', '264'])).
% 32.54/32.74  thf('266', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.74  thf('267', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))
% 32.54/32.74           = (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['85', '86'])).
% 32.54/32.74  thf('268', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('269', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('270', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('271', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ 
% 32.54/32.74           (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.74           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['265', '266', '267', '268', '269', '270'])).
% 32.54/32.74  thf('272', plain,
% 32.54/32.74      (![X50 : $i, X51 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X50)
% 32.54/32.74          | (v2_funct_1 @ (k8_relat_1 @ X51 @ X50))
% 32.54/32.74          | ~ (v1_funct_1 @ X50)
% 32.54/32.74          | ~ (v1_relat_1 @ X50))),
% 32.54/32.74      inference('cnf', [status(esa)], [t99_funct_1])).
% 32.54/32.74  thf('273', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v2_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74          | ~ (v1_relat_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.74          | ~ (v1_funct_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.74          | ~ (v2_funct_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['271', '272'])).
% 32.54/32.74  thf('274', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.74  thf('275', plain,
% 32.54/32.74      (![X32 : $i, X33 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X32)
% 32.54/32.74          | ~ (v1_relat_1 @ X32)
% 32.54/32.74          | (v1_relat_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.74  thf('276', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['274', '275'])).
% 32.54/32.74  thf('277', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('278', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('279', plain,
% 32.54/32.74      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.74  thf('280', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.74  thf('281', plain,
% 32.54/32.74      (![X32 : $i, X33 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X32)
% 32.54/32.74          | ~ (v1_relat_1 @ X32)
% 32.54/32.74          | (v1_funct_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.74  thf('282', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['280', '281'])).
% 32.54/32.74  thf('283', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('284', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('285', plain,
% 32.54/32.74      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.74  thf('286', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.74  thf('287', plain,
% 32.54/32.74      (![X48 : $i, X49 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X48)
% 32.54/32.74          | (v2_funct_1 @ (k7_relat_1 @ X48 @ X49))
% 32.54/32.74          | ~ (v1_funct_1 @ X48)
% 32.54/32.74          | ~ (v1_relat_1 @ X48))),
% 32.54/32.74      inference('cnf', [status(esa)], [t84_funct_1])).
% 32.54/32.74  thf('288', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74          | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['286', '287'])).
% 32.54/32.74  thf('289', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('290', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('291', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.74  thf('292', plain,
% 32.54/32.74      (![X0 : $i]: (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 32.54/32.74  thf('293', plain,
% 32.54/32.74      (![X0 : $i]: (v2_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['273', '279', '285', '292'])).
% 32.54/32.74  thf('294', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('295', plain,
% 32.54/32.74      (![X34 : $i, X35 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.74          | ~ (v1_funct_1 @ X35)
% 32.54/32.74          | ~ (v1_relat_1 @ X35))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.74  thf('296', plain,
% 32.54/32.74      (![X47 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X47)
% 32.54/32.74          | ((k1_relat_1 @ X47) = (k2_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.74          | ~ (v1_funct_1 @ X47)
% 32.54/32.74          | ~ (v1_relat_1 @ X47))),
% 32.54/32.74      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.74  thf('297', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k2_relat_1 @ (k2_funct_1 @ (k8_relat_1 @ X1 @ X0))))
% 32.54/32.74          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['295', '296'])).
% 32.54/32.74  thf('298', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k2_relat_1 @ (k2_funct_1 @ (k8_relat_1 @ X1 @ X0))))
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('sup-', [status(thm)], ['294', '297'])).
% 32.54/32.74  thf('299', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k2_relat_1 @ (k2_funct_1 @ (k8_relat_1 @ X1 @ X0))))
% 32.54/32.74          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('simplify', [status(thm)], ['298'])).
% 32.54/32.74  thf('300', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74          | ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74              = (k2_relat_1 @ 
% 32.54/32.74                 (k2_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['293', '299'])).
% 32.54/32.74  thf('301', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('302', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('303', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))
% 32.54/32.74           = (k5_relat_1 @ (k4_relat_1 @ sk_B) @ (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['85', '86'])).
% 32.54/32.74  thf('304', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k10_relat_1 @ X1 @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['115', '116'])).
% 32.54/32.74  thf('305', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74            = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['303', '304'])).
% 32.54/32.74  thf('306', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('307', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['305', '306'])).
% 32.54/32.74  thf('308', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.74           = (k2_relat_1 @ 
% 32.54/32.74              (k2_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('demod', [status(thm)], ['300', '301', '302', '307'])).
% 32.54/32.74  thf('309', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ 
% 32.54/32.74           (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.74           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['265', '266', '267', '268', '269', '270'])).
% 32.54/32.74  thf('310', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v2_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_funct_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('simplify', [status(thm)], ['245'])).
% 32.54/32.74  thf('311', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74            = (k4_relat_1 @ 
% 32.54/32.74               (k8_relat_1 @ X0 @ 
% 32.54/32.74                (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))))
% 32.54/32.74          | ~ (v1_relat_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.74          | ~ (v1_funct_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.74          | ~ (v2_funct_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['309', '310'])).
% 32.54/32.74  thf('312', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ 
% 32.54/32.74           (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.74           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['265', '266', '267', '268', '269', '270'])).
% 32.54/32.74  thf('313', plain,
% 32.54/32.74      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.74  thf('314', plain,
% 32.54/32.74      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.74  thf('315', plain,
% 32.54/32.74      (![X0 : $i]: (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 32.54/32.74  thf('316', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k2_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['311', '312', '313', '314', '315'])).
% 32.54/32.74  thf('317', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.74           = (k2_relat_1 @ 
% 32.54/32.74              (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('demod', [status(thm)], ['308', '316'])).
% 32.54/32.74  thf('318', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74           = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.74              (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['229', '230'])).
% 32.54/32.74  thf('319', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k10_relat_1 @ X1 @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['115', '116'])).
% 32.54/32.74  thf('320', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k1_relat_1 @ 
% 32.54/32.74            (k8_relat_1 @ X0 @ 
% 32.54/32.74             (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 32.54/32.74            = (k10_relat_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['318', '319'])).
% 32.54/32.74  thf('321', plain,
% 32.54/32.74      ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['225', '226', '227', '228'])).
% 32.54/32.74  thf('322', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k1_relat_1 @ 
% 32.54/32.74           (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 32.54/32.74           = (k10_relat_1 @ 
% 32.54/32.74              (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['320', '321'])).
% 32.54/32.74  thf('323', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.74  thf('324', plain,
% 32.54/32.74      (![X32 : $i, X33 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X32)
% 32.54/32.74          | ~ (v1_relat_1 @ X32)
% 32.54/32.74          | (v1_relat_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.74  thf('325', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['323', '324'])).
% 32.54/32.74  thf('326', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('327', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 32.54/32.74  thf('328', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['325', '326', '327'])).
% 32.54/32.74  thf('329', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.74  thf('330', plain,
% 32.54/32.74      (![X32 : $i, X33 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X32)
% 32.54/32.74          | ~ (v1_relat_1 @ X32)
% 32.54/32.74          | (v1_funct_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.74  thf('331', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['329', '330'])).
% 32.54/32.74  thf('332', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('333', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 32.54/32.74  thf('334', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['331', '332', '333'])).
% 32.54/32.74  thf('335', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.74  thf('336', plain,
% 32.54/32.74      (![X48 : $i, X49 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X48)
% 32.54/32.74          | (v2_funct_1 @ (k7_relat_1 @ X48 @ X49))
% 32.54/32.74          | ~ (v1_funct_1 @ X48)
% 32.54/32.74          | ~ (v1_relat_1 @ X48))),
% 32.54/32.74      inference('cnf', [status(esa)], [t84_funct_1])).
% 32.54/32.74  thf('337', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74          | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['335', '336'])).
% 32.54/32.74  thf('338', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('339', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 32.54/32.74  thf('340', plain, ((v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 32.54/32.74  thf('341', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['337', '338', '339', '340'])).
% 32.54/32.74  thf('342', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.74           = (k10_relat_1 @ 
% 32.54/32.74              (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['236', '317', '322', '328', '334', '341'])).
% 32.54/32.74  thf('343', plain,
% 32.54/32.74      (![X42 : $i, X43 : $i, X44 : $i]:
% 32.54/32.74         (((k10_relat_1 @ (k7_relat_1 @ X43 @ X42) @ X44)
% 32.54/32.74            = (k3_xboole_0 @ X42 @ (k10_relat_1 @ X43 @ X44)))
% 32.54/32.74          | ~ (v1_relat_1 @ X43))),
% 32.54/32.74      inference('cnf', [status(esa)], [t139_funct_1])).
% 32.54/32.74  thf('344', plain,
% 32.54/32.74      (![X32 : $i, X33 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X32)
% 32.54/32.74          | ~ (v1_relat_1 @ X32)
% 32.54/32.74          | (v1_relat_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.74      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.74  thf('345', plain,
% 32.54/32.74      (![X12 : $i, X13 : $i]:
% 32.54/32.74         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.74          | ~ (v1_relat_1 @ X12))),
% 32.54/32.74      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.74  thf('346', plain,
% 32.54/32.74      (![X9 : $i]:
% 32.54/32.74         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.74      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.74  thf('347', plain,
% 32.54/32.74      (![X7 : $i, X8 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.74          | ~ (v1_relat_1 @ X7))),
% 32.54/32.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.74  thf('348', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k10_relat_1 @ X1 @ X0))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['115', '116'])).
% 32.54/32.74  thf('349', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1))
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('sup+', [status(thm)], ['347', '348'])).
% 32.54/32.74  thf('350', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1)))),
% 32.54/32.74      inference('simplify', [status(thm)], ['349'])).
% 32.54/32.74  thf('351', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ X0)
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('sup+', [status(thm)], ['346', '350'])).
% 32.54/32.74  thf('352', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X0)
% 32.54/32.74          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 32.54/32.74      inference('simplify', [status(thm)], ['351'])).
% 32.54/32.74  thf('353', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 32.54/32.74      inference('sup+', [status(thm)], ['345', '352'])).
% 32.54/32.74  thf('354', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['344', '353'])).
% 32.54/32.74  thf('355', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 32.54/32.74          | ~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('simplify', [status(thm)], ['354'])).
% 32.54/32.74  thf('356', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ~ (v1_funct_1 @ X1))),
% 32.54/32.74      inference('sup+', [status(thm)], ['343', '355'])).
% 32.54/32.74  thf('357', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (~ (v1_funct_1 @ X1)
% 32.54/32.74          | ~ (v1_relat_1 @ X1)
% 32.54/32.74          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.74              = (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))))),
% 32.54/32.74      inference('simplify', [status(thm)], ['356'])).
% 32.54/32.74  thf('358', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k1_relat_1 @ 
% 32.54/32.74            (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.74             X0))
% 32.54/32.74            = (k3_xboole_0 @ X0 @ 
% 32.54/32.74               (k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.74                (k9_relat_1 @ 
% 32.54/32.74                 (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ X0))))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['342', '357'])).
% 32.54/32.74  thf('359', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('360', plain,
% 32.54/32.74      (![X7 : $i, X8 : $i]:
% 32.54/32.74         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.74          | ~ (v1_relat_1 @ X7))),
% 32.54/32.74      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.74  thf('361', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74           = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 32.54/32.74              (k6_relat_1 @ X0)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['359', '360'])).
% 32.54/32.74  thf('362', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 32.54/32.74          | ~ (v1_relat_1 @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['142', '143'])).
% 32.54/32.74  thf('363', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74            = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 32.54/32.74               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['361', '362'])).
% 32.54/32.74  thf('364', plain,
% 32.54/32.74      ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['225', '226', '227', '228'])).
% 32.54/32.74  thf('365', plain,
% 32.54/32.74      (![X28 : $i, X29 : $i]:
% 32.54/32.74         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 32.54/32.74          | ~ (v1_relat_1 @ X29))),
% 32.54/32.74      inference('cnf', [status(esa)], [t94_relat_1])).
% 32.54/32.74  thf('366', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ X0)
% 32.54/32.74           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 32.54/32.74              (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['364', '365'])).
% 32.54/32.74  thf('367', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('368', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.74              X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['363', '366', '367'])).
% 32.54/32.74  thf('369', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ X0)
% 32.54/32.74           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 32.54/32.74              (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('sup-', [status(thm)], ['364', '365'])).
% 32.54/32.74  thf('370', plain,
% 32.54/32.74      (![X16 : $i, X17 : $i]:
% 32.54/32.74         (~ (v1_relat_1 @ X16)
% 32.54/32.74          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 32.54/32.74              = (k10_relat_1 @ X17 @ (k1_relat_1 @ X16)))
% 32.54/32.74          | ~ (v1_relat_1 @ X17))),
% 32.54/32.74      inference('cnf', [status(esa)], [t182_relat_1])).
% 32.54/32.74  thf('371', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 32.54/32.74      inference('demod', [status(thm)], ['118', '119', '125', '126', '127'])).
% 32.54/32.74  thf('372', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 32.54/32.74            = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('sup+', [status(thm)], ['370', '371'])).
% 32.54/32.74  thf('373', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.74      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.74  thf('374', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 32.54/32.74            = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['372', '373'])).
% 32.54/32.74  thf('375', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         (((k3_xboole_0 @ 
% 32.54/32.74            (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))) @ 
% 32.54/32.74            X0)
% 32.54/32.74            = (k1_relat_1 @ 
% 32.54/32.74               (k7_relat_1 @ 
% 32.54/32.74                (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ X0)))
% 32.54/32.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['369', '374'])).
% 32.54/32.74  thf('376', plain,
% 32.54/32.74      (((k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74         = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['220', '221', '222'])).
% 32.54/32.74  thf('377', plain,
% 32.54/32.74      (![X47 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X47)
% 32.54/32.74          | ((k2_relat_1 @ X47) = (k1_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.74          | ~ (v1_funct_1 @ X47)
% 32.54/32.74          | ~ (v1_relat_1 @ X47))),
% 32.54/32.74      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.74  thf('378', plain,
% 32.54/32.74      ((((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74          = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 32.54/32.74        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('sup+', [status(thm)], ['376', '377'])).
% 32.54/32.74  thf('379', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.74  thf('380', plain,
% 32.54/32.74      (![X47 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X47)
% 32.54/32.74          | ((k1_relat_1 @ X47) = (k2_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.74          | ~ (v1_funct_1 @ X47)
% 32.54/32.74          | ~ (v1_relat_1 @ X47))),
% 32.54/32.74      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.74  thf('381', plain,
% 32.54/32.74      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74        | ((k1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74            = (k2_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('sup-', [status(thm)], ['379', '380'])).
% 32.54/32.74  thf('382', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.74  thf('383', plain,
% 32.54/32.74      (((k2_funct_1 @ (k4_relat_1 @ sk_B)) = (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)],
% 32.54/32.74                ['150', '157', '158', '165', '166', '167', '168', '169', '170'])).
% 32.54/32.74  thf('384', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.74  thf('385', plain,
% 32.54/32.74      (((k1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74         = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['381', '382', '383', '384'])).
% 32.54/32.74  thf('386', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.74  thf('387', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 32.54/32.74  thf('388', plain, ((v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 32.54/32.74  thf('389', plain,
% 32.54/32.74      (((k1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.74         = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('demod', [status(thm)], ['378', '385', '386', '387', '388'])).
% 32.54/32.74  thf('390', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.74  thf('391', plain,
% 32.54/32.74      (![X47 : $i]:
% 32.54/32.74         (~ (v2_funct_1 @ X47)
% 32.54/32.74          | ((k2_relat_1 @ X47) = (k1_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.74          | ~ (v1_funct_1 @ X47)
% 32.54/32.74          | ~ (v1_relat_1 @ X47))),
% 32.54/32.74      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.74  thf('392', plain,
% 32.54/32.74      ((((k2_relat_1 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.74        | ~ (v1_relat_1 @ sk_B)
% 32.54/32.74        | ~ (v1_funct_1 @ sk_B)
% 32.54/32.74        | ~ (v2_funct_1 @ sk_B))),
% 32.54/32.74      inference('sup+', [status(thm)], ['390', '391'])).
% 32.54/32.74  thf('393', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('394', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('395', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.74  thf('396', plain,
% 32.54/32.74      (((k2_relat_1 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.74      inference('demod', [status(thm)], ['392', '393', '394', '395'])).
% 32.54/32.74  thf('397', plain,
% 32.54/32.74      (((k2_relat_1 @ sk_B)
% 32.54/32.74         = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.74      inference('demod', [status(thm)], ['389', '396'])).
% 32.54/32.74  thf('398', plain,
% 32.54/32.74      ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.74      inference('demod', [status(thm)], ['225', '226', '227', '228'])).
% 32.54/32.74  thf('399', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)
% 32.54/32.74           = (k1_relat_1 @ 
% 32.54/32.74              (k7_relat_1 @ 
% 32.54/32.74               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ X0)))),
% 32.54/32.74      inference('demod', [status(thm)], ['375', '397', '398'])).
% 32.54/32.74  thf('400', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.74              X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['363', '366', '367'])).
% 32.54/32.74  thf('401', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)
% 32.54/32.74           = (k1_relat_1 @ 
% 32.54/32.74              (k4_relat_1 @ 
% 32.54/32.74               (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 32.54/32.74      inference('demod', [status(thm)], ['399', '400'])).
% 32.54/32.74  thf('402', plain,
% 32.54/32.74      (![X0 : $i]:
% 32.54/32.74         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.74           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.74      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.74  thf('403', plain,
% 32.54/32.74      (![X0 : $i, X1 : $i]:
% 32.54/32.74         (((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.75            = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v2_funct_1 @ X1)
% 32.54/32.75          | ~ (v1_funct_1 @ X1)
% 32.54/32.75          | ~ (v1_relat_1 @ X1))),
% 32.54/32.75      inference('simplify', [status(thm)], ['184'])).
% 32.54/32.75  thf('404', plain,
% 32.54/32.75      (![X31 : $i]:
% 32.54/32.75         ((v1_funct_1 @ (k2_funct_1 @ X31))
% 32.54/32.75          | ~ (v2_funct_1 @ X31)
% 32.54/32.75          | ~ (v1_funct_1 @ X31)
% 32.54/32.75          | ~ (v1_relat_1 @ X31))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.75  thf('405', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((v1_funct_1 @ (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ X1)
% 32.54/32.75          | ~ (v1_funct_1 @ X1)
% 32.54/32.75          | ~ (v2_funct_1 @ X1)
% 32.54/32.75          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v2_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['403', '404'])).
% 32.54/32.75  thf('406', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v2_funct_1 @ (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75          | ~ (v1_funct_1 @ (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | (v1_funct_1 @ 
% 32.54/32.75             (k4_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['402', '405'])).
% 32.54/32.75  thf('407', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('408', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('409', plain,
% 32.54/32.75      (![X0 : $i]: (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 32.54/32.75  thf('410', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('411', plain,
% 32.54/32.75      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.75  thf('412', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.75  thf('413', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.75  thf('414', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('415', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('416', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['406', '407', '408', '409', '410', '411', '412', '413', 
% 32.54/32.75                 '414', '415'])).
% 32.54/32.75  thf('417', plain,
% 32.54/32.75      (![X9 : $i]:
% 32.54/32.75         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.75      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.75  thf('418', plain,
% 32.54/32.75      (![X34 : $i, X35 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.75          | ~ (v1_funct_1 @ X35)
% 32.54/32.75          | ~ (v1_relat_1 @ X35))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.75  thf('419', plain,
% 32.54/32.75      (![X50 : $i, X51 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X50)
% 32.54/32.75          | (v2_funct_1 @ (k8_relat_1 @ X51 @ X50))
% 32.54/32.75          | ~ (v1_funct_1 @ X50)
% 32.54/32.75          | ~ (v1_relat_1 @ X50))),
% 32.54/32.75      inference('cnf', [status(esa)], [t99_funct_1])).
% 32.54/32.75  thf('420', plain,
% 32.54/32.75      (![X34 : $i, X35 : $i]:
% 32.54/32.75         ((v1_funct_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.75          | ~ (v1_funct_1 @ X35)
% 32.54/32.75          | ~ (v1_relat_1 @ X35))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.75  thf('421', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75            = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0))),
% 32.54/32.75      inference('simplify', [status(thm)], ['245'])).
% 32.54/32.75  thf('422', plain,
% 32.54/32.75      (![X31 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k2_funct_1 @ X31))
% 32.54/32.75          | ~ (v2_funct_1 @ X31)
% 32.54/32.75          | ~ (v1_funct_1 @ X31)
% 32.54/32.75          | ~ (v1_relat_1 @ X31))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.75  thf('423', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v1_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['421', '422'])).
% 32.54/32.75  thf('424', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['420', '423'])).
% 32.54/32.75  thf('425', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0))),
% 32.54/32.75      inference('simplify', [status(thm)], ['424'])).
% 32.54/32.75  thf('426', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['419', '425'])).
% 32.54/32.75  thf('427', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0))),
% 32.54/32.75      inference('simplify', [status(thm)], ['426'])).
% 32.54/32.75  thf('428', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['418', '427'])).
% 32.54/32.75  thf('429', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0))),
% 32.54/32.75      inference('simplify', [status(thm)], ['428'])).
% 32.54/32.75  thf('430', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k4_relat_1 @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v2_funct_1 @ X0))),
% 32.54/32.75      inference('sup+', [status(thm)], ['417', '429'])).
% 32.54/32.75  thf('431', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 32.54/32.75      inference('simplify', [status(thm)], ['430'])).
% 32.54/32.75  thf('432', plain,
% 32.54/32.75      (![X47 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X47)
% 32.54/32.75          | ((k1_relat_1 @ X47) = (k2_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.75          | ~ (v1_funct_1 @ X47)
% 32.54/32.75          | ~ (v1_relat_1 @ X47))),
% 32.54/32.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.75  thf('433', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 32.54/32.75          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 32.54/32.75              = (k2_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ X0))))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ X0)))),
% 32.54/32.75      inference('sup-', [status(thm)], ['431', '432'])).
% 32.54/32.75  thf('434', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ 
% 32.54/32.75             (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))
% 32.54/32.75          | ((k1_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))
% 32.54/32.75              = (k2_relat_1 @ 
% 32.54/32.75                 (k2_funct_1 @ 
% 32.54/32.75                  (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['416', '433'])).
% 32.54/32.75  thf('435', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('436', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.75            = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v2_funct_1 @ X1)
% 32.54/32.75          | ~ (v1_funct_1 @ X1)
% 32.54/32.75          | ~ (v1_relat_1 @ X1))),
% 32.54/32.75      inference('simplify', [status(thm)], ['184'])).
% 32.54/32.75  thf('437', plain,
% 32.54/32.75      (![X31 : $i]:
% 32.54/32.75         ((v2_funct_1 @ (k2_funct_1 @ X31))
% 32.54/32.75          | ~ (v2_funct_1 @ X31)
% 32.54/32.75          | ~ (v1_funct_1 @ X31)
% 32.54/32.75          | ~ (v1_relat_1 @ X31))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.75  thf('438', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((v2_funct_1 @ (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ X1)
% 32.54/32.75          | ~ (v1_funct_1 @ X1)
% 32.54/32.75          | ~ (v2_funct_1 @ X1)
% 32.54/32.75          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v2_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['436', '437'])).
% 32.54/32.75  thf('439', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v2_funct_1 @ (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75          | ~ (v1_funct_1 @ (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | (v2_funct_1 @ 
% 32.54/32.75             (k4_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['435', '438'])).
% 32.54/32.75  thf('440', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('441', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('442', plain,
% 32.54/32.75      (![X0 : $i]: (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 32.54/32.75  thf('443', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('444', plain,
% 32.54/32.75      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.75  thf('445', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.75  thf('446', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.75  thf('447', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('448', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('449', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['439', '440', '441', '442', '443', '444', '445', '446', 
% 32.54/32.75                 '447', '448'])).
% 32.54/32.75  thf('450', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('451', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.75            = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v2_funct_1 @ X1)
% 32.54/32.75          | ~ (v1_funct_1 @ X1)
% 32.54/32.75          | ~ (v1_relat_1 @ X1))),
% 32.54/32.75      inference('simplify', [status(thm)], ['184'])).
% 32.54/32.75  thf('452', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75            = (k4_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['450', '451'])).
% 32.54/32.75  thf('453', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('454', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('455', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.75  thf('456', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.75  thf('457', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75           = (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['452', '453', '454', '455', '456'])).
% 32.54/32.75  thf('458', plain,
% 32.54/32.75      (![X47 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X47)
% 32.54/32.75          | ((k2_relat_1 @ X47) = (k1_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.75          | ~ (v1_funct_1 @ X47)
% 32.54/32.75          | ~ (v1_relat_1 @ X47))),
% 32.54/32.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.75  thf('459', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75            = (k1_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['457', '458'])).
% 32.54/32.75  thf('460', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('461', plain,
% 32.54/32.75      (![X12 : $i, X13 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.75          | ~ (v1_relat_1 @ X12))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.75  thf('462', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75            = (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['460', '461'])).
% 32.54/32.75  thf('463', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('464', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['462', '463'])).
% 32.54/32.75  thf('465', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('466', plain,
% 32.54/32.75      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.75  thf('467', plain,
% 32.54/32.75      (![X0 : $i]: (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 32.54/32.75  thf('468', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k1_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))))),
% 32.54/32.75      inference('demod', [status(thm)], ['459', '464', '465', '466', '467'])).
% 32.54/32.75  thf('469', plain,
% 32.54/32.75      (![X0 : $i]: (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 32.54/32.75  thf('470', plain,
% 32.54/32.75      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.75  thf('471', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('472', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k2_relat_1 @ 
% 32.54/32.75              (k2_funct_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['434', '449', '468', '469', '470', '471'])).
% 32.54/32.75  thf('473', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['406', '407', '408', '409', '410', '411', '412', '413', 
% 32.54/32.75                 '414', '415'])).
% 32.54/32.75  thf('474', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 32.54/32.75      inference('simplify', [status(thm)], ['430'])).
% 32.54/32.75  thf('475', plain,
% 32.54/32.75      (![X30 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X30)
% 32.54/32.75          | ((k2_funct_1 @ X30) = (k4_relat_1 @ X30))
% 32.54/32.75          | ~ (v1_funct_1 @ X30)
% 32.54/32.75          | ~ (v1_relat_1 @ X30))),
% 32.54/32.75      inference('cnf', [status(esa)], [d9_funct_1])).
% 32.54/32.75  thf('476', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 32.54/32.75          | ((k2_funct_1 @ (k4_relat_1 @ X0))
% 32.54/32.75              = (k4_relat_1 @ (k4_relat_1 @ X0)))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ X0)))),
% 32.54/32.75      inference('sup-', [status(thm)], ['474', '475'])).
% 32.54/32.75  thf('477', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ 
% 32.54/32.75             (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))
% 32.54/32.75          | ((k2_funct_1 @ 
% 32.54/32.75              (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))
% 32.54/32.75              = (k4_relat_1 @ 
% 32.54/32.75                 (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['473', '476'])).
% 32.54/32.75  thf('478', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['439', '440', '441', '442', '443', '444', '445', '446', 
% 32.54/32.75                 '447', '448'])).
% 32.54/32.75  thf('479', plain,
% 32.54/32.75      (![X0 : $i]: (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 32.54/32.75  thf('480', plain,
% 32.54/32.75      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.75  thf('481', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('482', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))
% 32.54/32.75           = (k4_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))))),
% 32.54/32.75      inference('demod', [status(thm)], ['477', '478', '479', '480', '481'])).
% 32.54/32.75  thf('483', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k2_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))))),
% 32.54/32.75      inference('demod', [status(thm)], ['472', '482'])).
% 32.54/32.75  thf('484', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup-', [status(thm)], ['252', '253'])).
% 32.54/32.75  thf('485', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('486', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['484', '485'])).
% 32.54/32.75  thf('487', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 32.54/32.75            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ X1))),
% 32.54/32.75      inference('demod', [status(thm)], ['70', '71'])).
% 32.54/32.75  thf('488', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75            = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 32.54/32.75               (k6_relat_1 @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['486', '487'])).
% 32.54/32.75  thf('489', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 32.54/32.75              (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('sup-', [status(thm)], ['359', '360'])).
% 32.54/32.75  thf('490', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('491', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['488', '489', '490'])).
% 32.54/32.75  thf('492', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k2_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ 
% 32.54/32.75               (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))),
% 32.54/32.75      inference('demod', [status(thm)], ['483', '491'])).
% 32.54/32.75  thf('493', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.75              X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['363', '366', '367'])).
% 32.54/32.75  thf('494', plain,
% 32.54/32.75      (![X12 : $i, X13 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.75          | ~ (v1_relat_1 @ X12))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.75  thf('495', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k2_relat_1 @ 
% 32.54/32.75            (k4_relat_1 @ 
% 32.54/32.75             (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 32.54/32.75            = (k9_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['493', '494'])).
% 32.54/32.75  thf('496', plain,
% 32.54/32.75      ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['225', '226', '227', '228'])).
% 32.54/32.75  thf('497', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_relat_1 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.75              X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['495', '496'])).
% 32.54/32.75  thf('498', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.75              X0))),
% 32.54/32.75      inference('sup+', [status(thm)], ['492', '497'])).
% 32.54/32.75  thf('499', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['265', '266', '267', '268', '269', '270'])).
% 32.54/32.75  thf(t128_relat_1, axiom,
% 32.54/32.75    (![A:$i,B:$i]:
% 32.54/32.75     ( ( v1_relat_1 @ B ) =>
% 32.54/32.75       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ A @ B ) ) = ( k8_relat_1 @ A @ B ) ) ))).
% 32.54/32.75  thf('500', plain,
% 32.54/32.75      (![X10 : $i, X11 : $i]:
% 32.54/32.75         (((k8_relat_1 @ X10 @ (k8_relat_1 @ X10 @ X11))
% 32.54/32.75            = (k8_relat_1 @ X10 @ X11))
% 32.54/32.75          | ~ (v1_relat_1 @ X11))),
% 32.54/32.75      inference('cnf', [status(esa)], [t128_relat_1])).
% 32.54/32.75  thf('501', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75            = (k8_relat_1 @ X0 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))))
% 32.54/32.75          | ~ (v1_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['499', '500'])).
% 32.54/32.75  thf('502', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['265', '266', '267', '268', '269', '270'])).
% 32.54/32.75  thf('503', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('504', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['501', '502', '503'])).
% 32.54/32.75  thf('505', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75            = (k2_relat_1 @ (k2_funct_1 @ (k8_relat_1 @ X1 @ X0))))
% 32.54/32.75          | ~ (v2_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0))),
% 32.54/32.75      inference('simplify', [status(thm)], ['298'])).
% 32.54/32.75  thf('506', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75          | ((k1_relat_1 @ 
% 32.54/32.75              (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75              = (k2_relat_1 @ 
% 32.54/32.75                 (k2_funct_1 @ 
% 32.54/32.75                  (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['504', '505'])).
% 32.54/32.75  thf('507', plain,
% 32.54/32.75      (![X0 : $i]: (v2_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['273', '279', '285', '292'])).
% 32.54/32.75  thf('508', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['265', '266', '267', '268', '269', '270'])).
% 32.54/32.75  thf('509', plain,
% 32.54/32.75      (![X34 : $i, X35 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.75          | ~ (v1_funct_1 @ X35)
% 32.54/32.75          | ~ (v1_relat_1 @ X35))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.75  thf('510', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.75          | ~ (v1_funct_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['508', '509'])).
% 32.54/32.75  thf('511', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('512', plain,
% 32.54/32.75      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.75  thf('513', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['510', '511', '512'])).
% 32.54/32.75  thf('514', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['265', '266', '267', '268', '269', '270'])).
% 32.54/32.75  thf('515', plain,
% 32.54/32.75      (![X34 : $i, X35 : $i]:
% 32.54/32.75         ((v1_funct_1 @ (k8_relat_1 @ X34 @ X35))
% 32.54/32.75          | ~ (v1_funct_1 @ X35)
% 32.54/32.75          | ~ (v1_relat_1 @ X35))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc9_funct_1])).
% 32.54/32.75  thf('516', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((v1_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))
% 32.54/32.75          | ~ (v1_funct_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['514', '515'])).
% 32.54/32.75  thf('517', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('518', plain,
% 32.54/32.75      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.75  thf('519', plain,
% 32.54/32.75      (![X0 : $i]: (v1_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['516', '517', '518'])).
% 32.54/32.75  thf('520', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['501', '502', '503'])).
% 32.54/32.75  thf('521', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['305', '306'])).
% 32.54/32.75  thf('522', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['501', '502', '503'])).
% 32.54/32.75  thf('523', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_funct_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['311', '312', '313', '314', '315'])).
% 32.54/32.75  thf('524', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.75  thf('525', plain,
% 32.54/32.75      (![X12 : $i, X13 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.75          | ~ (v1_relat_1 @ X12))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.75  thf('526', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75            = (k9_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['524', '525'])).
% 32.54/32.75  thf('527', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.75  thf('528', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['526', '527'])).
% 32.54/32.75  thf('529', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['506', '507', '513', '519', '520', '521', '522', '523', '528'])).
% 32.54/32.75  thf(t148_funct_1, axiom,
% 32.54/32.75    (![A:$i,B:$i]:
% 32.54/32.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 32.54/32.75       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 32.54/32.75         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 32.54/32.75  thf('530', plain,
% 32.54/32.75      (![X45 : $i, X46 : $i]:
% 32.54/32.75         (((k9_relat_1 @ X46 @ (k10_relat_1 @ X46 @ X45))
% 32.54/32.75            = (k3_xboole_0 @ X45 @ (k9_relat_1 @ X46 @ (k1_relat_1 @ X46))))
% 32.54/32.75          | ~ (v1_funct_1 @ X46)
% 32.54/32.75          | ~ (v1_relat_1 @ X46))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_funct_1])).
% 32.54/32.75  thf('531', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k9_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 32.54/32.75            (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))
% 32.54/32.75            = (k3_xboole_0 @ X0 @ 
% 32.54/32.75               (k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75                (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['529', '530'])).
% 32.54/32.75  thf('532', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['506', '507', '513', '519', '520', '521', '522', '523', '528'])).
% 32.54/32.75  thf('533', plain,
% 32.54/32.75      (((k2_funct_1 @ (k4_relat_1 @ sk_B)) = (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['150', '157', '158', '165', '166', '167', '168', '169', '170'])).
% 32.54/32.75  thf('534', plain,
% 32.54/32.75      (![X47 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X47)
% 32.54/32.75          | ((k2_relat_1 @ X47) = (k1_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.75          | ~ (v1_funct_1 @ X47)
% 32.54/32.75          | ~ (v1_relat_1 @ X47))),
% 32.54/32.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.75  thf('535', plain,
% 32.54/32.75      ((((k2_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['533', '534'])).
% 32.54/32.75  thf('536', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('537', plain,
% 32.54/32.75      (![X47 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X47)
% 32.54/32.75          | ((k1_relat_1 @ X47) = (k2_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.75          | ~ (v1_funct_1 @ X47)
% 32.54/32.75          | ~ (v1_relat_1 @ X47))),
% 32.54/32.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.75  thf('538', plain,
% 32.54/32.75      ((~ (v1_funct_1 @ sk_B)
% 32.54/32.75        | ((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 32.54/32.75        | ~ (v2_funct_1 @ sk_B))),
% 32.54/32.75      inference('sup-', [status(thm)], ['536', '537'])).
% 32.54/32.75  thf('539', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('540', plain, (((k2_funct_1 @ sk_B) = (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.54/32.75  thf('541', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('542', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['538', '539', '540', '541'])).
% 32.54/32.75  thf('543', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('544', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.75  thf('545', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.75  thf('546', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['535', '542', '543', '544', '545'])).
% 32.54/32.75  thf('547', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['538', '539', '540', '541'])).
% 32.54/32.75  thf('548', plain,
% 32.54/32.75      (![X9 : $i]:
% 32.54/32.75         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.75      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.75  thf('549', plain,
% 32.54/32.75      ((((k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k4_relat_1 @ sk_B))
% 32.54/32.75          = (k4_relat_1 @ sk_B))
% 32.54/32.75        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['547', '548'])).
% 32.54/32.75  thf('550', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('551', plain,
% 32.54/32.75      (((k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k4_relat_1 @ sk_B))
% 32.54/32.75         = (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['549', '550'])).
% 32.54/32.75  thf('552', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X0)
% 32.54/32.75          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1)))),
% 32.54/32.75      inference('simplify', [status(thm)], ['349'])).
% 32.54/32.75  thf('553', plain,
% 32.54/32.75      ((((k1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))
% 32.54/32.75        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['551', '552'])).
% 32.54/32.75  thf('554', plain,
% 32.54/32.75      (((k2_relat_1 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['392', '393', '394', '395'])).
% 32.54/32.75  thf('555', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('556', plain,
% 32.54/32.75      (((k2_relat_1 @ sk_B)
% 32.54/32.75         = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['553', '554', '555'])).
% 32.54/32.75  thf('557', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.75  thf('558', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 32.54/32.75  thf('559', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['531', '532', '546', '556', '557', '558'])).
% 32.54/32.75  thf('560', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75           = (k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['452', '453', '454', '455', '456'])).
% 32.54/32.75  thf('561', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['488', '489', '490'])).
% 32.54/32.75  thf('562', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['560', '561'])).
% 32.54/32.75  thf('563', plain,
% 32.54/32.75      (![X47 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X47)
% 32.54/32.75          | ((k2_relat_1 @ X47) = (k1_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.75          | ~ (v1_funct_1 @ X47)
% 32.54/32.75          | ~ (v1_relat_1 @ X47))),
% 32.54/32.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.75  thf('564', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75            = (k1_relat_1 @ 
% 32.54/32.75               (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['562', '563'])).
% 32.54/32.75  thf('565', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['462', '463'])).
% 32.54/32.75  thf('566', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 32.54/32.75              (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('sup-', [status(thm)], ['359', '360'])).
% 32.54/32.75  thf('567', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75            = (k10_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ X1))),
% 32.54/32.75      inference('demod', [status(thm)], ['115', '116'])).
% 32.54/32.75  thf('568', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75            = (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['566', '567'])).
% 32.54/32.75  thf('569', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.75  thf('570', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['568', '569'])).
% 32.54/32.75  thf('571', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('572', plain,
% 32.54/32.75      (![X0 : $i]: (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['282', '283', '284'])).
% 32.54/32.75  thf('573', plain,
% 32.54/32.75      (![X0 : $i]: (v2_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 32.54/32.75  thf('574', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['564', '565', '570', '571', '572', '573'])).
% 32.54/32.75  thf('575', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['559', '574'])).
% 32.54/32.75  thf('576', plain,
% 32.54/32.75      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['101', '102'])).
% 32.54/32.75  thf('577', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.75           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['106', '107', '108'])).
% 32.54/32.75  thf(t100_relat_1, axiom,
% 32.54/32.75    (![A:$i,B:$i,C:$i]:
% 32.54/32.75     ( ( v1_relat_1 @ C ) =>
% 32.54/32.75       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 32.54/32.75         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 32.54/32.75  thf('578', plain,
% 32.54/32.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 32.54/32.75         (((k7_relat_1 @ (k7_relat_1 @ X4 @ X5) @ X6)
% 32.54/32.75            = (k7_relat_1 @ X4 @ (k3_xboole_0 @ X5 @ X6)))
% 32.54/32.75          | ~ (v1_relat_1 @ X4))),
% 32.54/32.75      inference('cnf', [status(esa)], [t100_relat_1])).
% 32.54/32.75  thf('579', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.54/32.75         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 32.54/32.75            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['577', '578'])).
% 32.54/32.75  thf('580', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.75           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['106', '107', '108'])).
% 32.54/32.75  thf('581', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.75  thf('582', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 32.54/32.75           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 32.54/32.75      inference('demod', [status(thm)], ['579', '580', '581'])).
% 32.54/32.75  thf('583', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['576', '582'])).
% 32.54/32.75  thf('584', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.75           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['106', '107', '108'])).
% 32.54/32.75  thf('585', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 32.54/32.75      inference('demod', [status(thm)], ['583', '584'])).
% 32.54/32.75  thf('586', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X0)
% 32.54/32.75          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1)))),
% 32.54/32.75      inference('simplify', [status(thm)], ['349'])).
% 32.54/32.75  thf('587', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75            = (k10_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1))
% 32.54/32.75          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['585', '586'])).
% 32.54/32.75  thf('588', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k3_xboole_0 @ X1 @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['122', '123', '124'])).
% 32.54/32.75  thf('589', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 32.54/32.75      inference('demod', [status(thm)], ['118', '119', '125', '126', '127'])).
% 32.54/32.75  thf('590', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.75  thf('591', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['587', '588', '589', '590'])).
% 32.54/32.75  thf('592', plain,
% 32.54/32.75      ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['225', '226', '227', '228'])).
% 32.54/32.75  thf('593', plain,
% 32.54/32.75      (((k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75         = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['220', '221', '222'])).
% 32.54/32.75  thf('594', plain,
% 32.54/32.75      (![X31 : $i]:
% 32.54/32.75         ((v1_funct_1 @ (k2_funct_1 @ X31))
% 32.54/32.75          | ~ (v2_funct_1 @ X31)
% 32.54/32.75          | ~ (v1_funct_1 @ X31)
% 32.54/32.75          | ~ (v1_relat_1 @ X31))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.54/32.75  thf('595', plain,
% 32.54/32.75      (((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['593', '594'])).
% 32.54/32.75  thf('596', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.75  thf('597', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 32.54/32.75  thf('598', plain, ((v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 32.54/32.75  thf('599', plain,
% 32.54/32.75      ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['595', '596', '597', '598'])).
% 32.54/32.75  thf('600', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['358', '368', '401', '498', '575', '591', '592', '599'])).
% 32.54/32.75  thf('601', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 32.54/32.75      inference('demod', [status(thm)], ['583', '584'])).
% 32.54/32.75  thf('602', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.75           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['106', '107', '108'])).
% 32.54/32.75  thf('603', plain,
% 32.54/32.75      (![X12 : $i, X13 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.75          | ~ (v1_relat_1 @ X12))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.75  thf('604', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['602', '603'])).
% 32.54/32.75  thf('605', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.75  thf('606', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['604', '605'])).
% 32.54/32.75  thf('607', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['601', '606'])).
% 32.54/32.75  thf('608', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['604', '605'])).
% 32.54/32.75  thf('609', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['607', '608'])).
% 32.54/32.75  thf('610', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k6_relat_1 @ X0) @ (k2_relat_1 @ sk_B))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 32.54/32.75              (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['600', '609'])).
% 32.54/32.75  thf('611', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['358', '368', '401', '498', '575', '591', '592', '599'])).
% 32.54/32.75  thf('612', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['559', '574'])).
% 32.54/32.75  thf('613', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.75  thf('614', plain,
% 32.54/32.75      (![X42 : $i, X43 : $i, X44 : $i]:
% 32.54/32.75         (((k10_relat_1 @ (k7_relat_1 @ X43 @ X42) @ X44)
% 32.54/32.75            = (k3_xboole_0 @ X42 @ (k10_relat_1 @ X43 @ X44)))
% 32.54/32.75          | ~ (v1_relat_1 @ X43))),
% 32.54/32.75      inference('cnf', [status(esa)], [t139_funct_1])).
% 32.54/32.75  thf('615', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k10_relat_1 @ 
% 32.54/32.75            (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ X1)
% 32.54/32.75            = (k3_xboole_0 @ X0 @ 
% 32.54/32.75               (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X1)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['613', '614'])).
% 32.54/32.75  thf('616', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.75  thf('617', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k10_relat_1 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ X1)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ 
% 32.54/32.75              (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X1)))),
% 32.54/32.75      inference('demod', [status(thm)], ['615', '616'])).
% 32.54/32.75  thf('618', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['564', '565', '570', '571', '572', '573'])).
% 32.54/32.75  thf('619', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k10_relat_1 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ X1)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X1)))),
% 32.54/32.75      inference('demod', [status(thm)], ['617', '618'])).
% 32.54/32.75  thf('620', plain,
% 32.54/32.75      (![X45 : $i, X46 : $i]:
% 32.54/32.75         (((k9_relat_1 @ X46 @ (k10_relat_1 @ X46 @ X45))
% 32.54/32.75            = (k3_xboole_0 @ X45 @ (k9_relat_1 @ X46 @ (k1_relat_1 @ X46))))
% 32.54/32.75          | ~ (v1_funct_1 @ X46)
% 32.54/32.75          | ~ (v1_relat_1 @ X46))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_funct_1])).
% 32.54/32.75  thf('621', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 32.54/32.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 32.54/32.75  thf('622', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k9_relat_1 @ X0 @ 
% 32.54/32.75            (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 32.54/32.75            = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0))),
% 32.54/32.75      inference('sup+', [status(thm)], ['620', '621'])).
% 32.54/32.75  thf('623', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k9_relat_1 @ 
% 32.54/32.75            (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.75            (k3_xboole_0 @ X0 @ 
% 32.54/32.75             (k9_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75              (k9_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.75               (k1_relat_1 @ 
% 32.54/32.75                (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))))))
% 32.54/32.75            = (k9_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ 
% 32.54/32.75               (k1_relat_1 @ 
% 32.54/32.75                (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))))
% 32.54/32.75          | ~ (v1_funct_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75          | ~ (v1_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['619', '622'])).
% 32.54/32.75  thf('624', plain,
% 32.54/32.75      (![X28 : $i, X29 : $i]:
% 32.54/32.75         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 32.54/32.75          | ~ (v1_relat_1 @ X29))),
% 32.54/32.75      inference('cnf', [status(esa)], [t94_relat_1])).
% 32.54/32.75  thf('625', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['535', '542', '543', '544', '545'])).
% 32.54/32.75  thf('626', plain,
% 32.54/32.75      (![X16 : $i, X17 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X16)
% 32.54/32.75          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16))
% 32.54/32.75              = (k10_relat_1 @ X17 @ (k1_relat_1 @ X16)))
% 32.54/32.75          | ~ (v1_relat_1 @ X17))),
% 32.54/32.75      inference('cnf', [status(esa)], [t182_relat_1])).
% 32.54/32.75  thf('627', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75            = (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['625', '626'])).
% 32.54/32.75  thf('628', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.75  thf('629', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75            = (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['627', '628'])).
% 32.54/32.75  thf('630', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))
% 32.54/32.75            = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['624', '629'])).
% 32.54/32.75  thf('631', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 32.54/32.75      inference('demod', [status(thm)], ['118', '119', '125', '126', '127'])).
% 32.54/32.75  thf('632', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.75  thf('633', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.75  thf('634', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))
% 32.54/32.75           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['630', '631', '632', '633'])).
% 32.54/32.75  thf('635', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.75  thf('636', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['634', '635'])).
% 32.54/32.75  thf('637', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.75  thf('638', plain,
% 32.54/32.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 32.54/32.75         (((k7_relat_1 @ (k7_relat_1 @ X4 @ X5) @ X6)
% 32.54/32.75            = (k7_relat_1 @ X4 @ (k3_xboole_0 @ X5 @ X6)))
% 32.54/32.75          | ~ (v1_relat_1 @ X4))),
% 32.54/32.75      inference('cnf', [status(esa)], [t100_relat_1])).
% 32.54/32.75  thf('639', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k7_relat_1 @ 
% 32.54/32.75            (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ X1)
% 32.54/32.75            = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 32.54/32.75               (k3_xboole_0 @ X0 @ X1)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['637', '638'])).
% 32.54/32.75  thf('640', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['145', '179', '180'])).
% 32.54/32.75  thf('641', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.75  thf('642', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k7_relat_1 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ X1)
% 32.54/32.75           = (k4_relat_1 @ 
% 32.54/32.75              (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['639', '640', '641'])).
% 32.54/32.75  thf('643', plain,
% 32.54/32.75      (![X12 : $i, X13 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.75          | ~ (v1_relat_1 @ X12))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.75  thf('644', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k2_relat_1 @ 
% 32.54/32.75            (k4_relat_1 @ 
% 32.54/32.75             (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k4_relat_1 @ sk_B))))
% 32.54/32.75            = (k9_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ X1 @ (k4_relat_1 @ sk_B))) @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ X1 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['642', '643'])).
% 32.54/32.75  thf('645', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k2_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.75      inference('demod', [status(thm)], ['308', '316'])).
% 32.54/32.75  thf('646', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['325', '326', '327'])).
% 32.54/32.75  thf('647', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k3_xboole_0 @ X1 @ X0))
% 32.54/32.75           = (k9_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ (k8_relat_1 @ X1 @ (k4_relat_1 @ sk_B))) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['644', '645', '646'])).
% 32.54/32.75  thf('648', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['131', '132'])).
% 32.54/32.75  thf('649', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['538', '539', '540', '541'])).
% 32.54/32.75  thf(t168_relat_1, axiom,
% 32.54/32.75    (![A:$i,B:$i]:
% 32.54/32.75     ( ( v1_relat_1 @ B ) =>
% 32.54/32.75       ( ( k10_relat_1 @ B @ A ) =
% 32.54/32.75         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 32.54/32.75  thf('650', plain,
% 32.54/32.75      (![X14 : $i, X15 : $i]:
% 32.54/32.75         (((k10_relat_1 @ X14 @ X15)
% 32.54/32.75            = (k10_relat_1 @ X14 @ (k3_xboole_0 @ (k2_relat_1 @ X14) @ X15)))
% 32.54/32.75          | ~ (v1_relat_1 @ X14))),
% 32.54/32.75      inference('cnf', [status(esa)], [t168_relat_1])).
% 32.54/32.75  thf('651', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75            = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75               (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['649', '650'])).
% 32.54/32.75  thf('652', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('653', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75              (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['651', '652'])).
% 32.54/32.75  thf('654', plain,
% 32.54/32.75      (((k2_relat_1 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['392', '393', '394', '395'])).
% 32.54/32.75  thf('655', plain,
% 32.54/32.75      (![X45 : $i, X46 : $i]:
% 32.54/32.75         (((k9_relat_1 @ X46 @ (k10_relat_1 @ X46 @ X45))
% 32.54/32.75            = (k3_xboole_0 @ X45 @ (k9_relat_1 @ X46 @ (k1_relat_1 @ X46))))
% 32.54/32.75          | ~ (v1_funct_1 @ X46)
% 32.54/32.75          | ~ (v1_relat_1 @ X46))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_funct_1])).
% 32.54/32.75  thf('656', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k9_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75            (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75            = (k3_xboole_0 @ X0 @ 
% 32.54/32.75               (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B))))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['654', '655'])).
% 32.54/32.75  thf('657', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('658', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.75  thf('659', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ 
% 32.54/32.75              (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['656', '657', '658'])).
% 32.54/32.75  thf('660', plain,
% 32.54/32.75      (![X9 : $i]:
% 32.54/32.75         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.75      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.75  thf('661', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['462', '463'])).
% 32.54/32.75  thf('662', plain,
% 32.54/32.75      ((((k2_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          = (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B)))
% 32.54/32.75        | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['660', '661'])).
% 32.54/32.75  thf('663', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['538', '539', '540', '541'])).
% 32.54/32.75  thf('664', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('665', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B)
% 32.54/32.75         = (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['662', '663', '664'])).
% 32.54/32.75  thf('666', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['659', '665'])).
% 32.54/32.75  thf('667', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['587', '588', '589', '590'])).
% 32.54/32.75  thf('668', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k3_xboole_0 @ X1 @ X0))
% 32.54/32.75           = (k9_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ (k8_relat_1 @ X1 @ (k4_relat_1 @ sk_B))) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['644', '645', '646'])).
% 32.54/32.75  thf('669', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['587', '588', '589', '590'])).
% 32.54/32.75  thf('670', plain,
% 32.54/32.75      (((k2_relat_1 @ sk_B)
% 32.54/32.75         = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['553', '554', '555'])).
% 32.54/32.75  thf(t137_funct_1, axiom,
% 32.54/32.75    (![A:$i,B:$i,C:$i]:
% 32.54/32.75     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 32.54/32.75       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 32.54/32.75         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 32.54/32.75  thf('671', plain,
% 32.54/32.75      (![X39 : $i, X40 : $i, X41 : $i]:
% 32.54/32.75         (((k10_relat_1 @ X39 @ (k3_xboole_0 @ X40 @ X41))
% 32.54/32.75            = (k3_xboole_0 @ (k10_relat_1 @ X39 @ X40) @ 
% 32.54/32.75               (k10_relat_1 @ X39 @ X41)))
% 32.54/32.75          | ~ (v1_funct_1 @ X39)
% 32.54/32.75          | ~ (v1_relat_1 @ X39))),
% 32.54/32.75      inference('cnf', [status(esa)], [t137_funct_1])).
% 32.54/32.75  thf('672', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75            (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))
% 32.54/32.75            = (k3_xboole_0 @ (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ 
% 32.54/32.75               (k2_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['670', '671'])).
% 32.54/32.75  thf('673', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('674', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.75  thf('675', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))
% 32.54/32.75           = (k3_xboole_0 @ (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ 
% 32.54/32.75              (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['672', '673', '674'])).
% 32.54/32.75  thf('676', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['634', '635'])).
% 32.54/32.75  thf('677', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k3_xboole_0 @ X1 @ X0))
% 32.54/32.75           = (k9_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ (k8_relat_1 @ X1 @ (k4_relat_1 @ sk_B))) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['644', '645', '646'])).
% 32.54/32.75  thf('678', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['131', '132'])).
% 32.54/32.75  thf('679', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75              (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['651', '652'])).
% 32.54/32.75  thf('680', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_funct_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['331', '332', '333'])).
% 32.54/32.75  thf('681', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['325', '326', '327'])).
% 32.54/32.75  thf('682', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ 
% 32.54/32.75           (k2_relat_1 @ sk_B)) = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['623', '636', '647', '648', '653', '666', '667', '668', 
% 32.54/32.75                 '669', '675', '676', '677', '678', '679', '680', '681'])).
% 32.54/32.75  thf('683', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 32.54/32.75           (k2_relat_1 @ sk_B))
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75              (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['612', '682'])).
% 32.54/32.75  thf('684', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['559', '574'])).
% 32.54/32.75  thf('685', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 32.54/32.75           (k2_relat_1 @ sk_B)) = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['683', '684'])).
% 32.54/32.75  thf('686', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['607', '608'])).
% 32.54/32.75  thf('687', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ 
% 32.54/32.75           (k6_relat_1 @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 32.54/32.75           (k2_relat_1 @ sk_B))
% 32.54/32.75           = (k9_relat_1 @ 
% 32.54/32.75              (k6_relat_1 @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 32.54/32.75              (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['685', '686'])).
% 32.54/32.75  thf('688', plain,
% 32.54/32.75      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['101', '102'])).
% 32.54/32.75  thf('689', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['604', '605'])).
% 32.54/32.75  thf('690', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k6_relat_1 @ X0))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 32.54/32.75      inference('sup+', [status(thm)], ['688', '689'])).
% 32.54/32.75  thf('691', plain, (![X24 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 32.54/32.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 32.54/32.75  thf('692', plain,
% 32.54/32.75      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['690', '691'])).
% 32.54/32.75  thf('693', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ 
% 32.54/32.75           (k6_relat_1 @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))) @ 
% 32.54/32.75           (k2_relat_1 @ sk_B)) = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['687', '692'])).
% 32.54/32.75  thf('694', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ 
% 32.54/32.75           (k6_relat_1 @ (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)) @ 
% 32.54/32.75           (k2_relat_1 @ sk_B)) = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['611', '693'])).
% 32.54/32.75  thf('695', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 32.54/32.75      inference('demod', [status(thm)], ['583', '584'])).
% 32.54/32.75  thf('696', plain,
% 32.54/32.75      (![X28 : $i, X29 : $i]:
% 32.54/32.75         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 32.54/32.75          | ~ (v1_relat_1 @ X29))),
% 32.54/32.75      inference('cnf', [status(esa)], [t94_relat_1])).
% 32.54/32.75  thf('697', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 32.54/32.75          | ~ (v1_relat_1 @ X1))),
% 32.54/32.75      inference('demod', [status(thm)], ['142', '143'])).
% 32.54/32.75  thf('698', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 32.54/32.75            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 32.54/32.75               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 32.54/32.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 32.54/32.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['696', '697'])).
% 32.54/32.75  thf('699', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.75           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['106', '107', '108'])).
% 32.54/32.75  thf('700', plain,
% 32.54/32.75      (![X25 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X25)) = (k6_relat_1 @ X25))),
% 32.54/32.75      inference('cnf', [status(esa)], [t72_relat_1])).
% 32.54/32.75  thf('701', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.75  thf('702', plain,
% 32.54/32.75      (![X7 : $i, X8 : $i]:
% 32.54/32.75         (((k8_relat_1 @ X8 @ X7) = (k5_relat_1 @ X7 @ (k6_relat_1 @ X8)))
% 32.54/32.75          | ~ (v1_relat_1 @ X7))),
% 32.54/32.75      inference('cnf', [status(esa)], [t123_relat_1])).
% 32.54/32.75  thf('703', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 32.54/32.75           = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('sup-', [status(thm)], ['701', '702'])).
% 32.54/32.75  thf('704', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.75  thf('705', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.75  thf('706', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['698', '699', '700', '703', '704', '705'])).
% 32.54/32.75  thf('707', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['695', '706'])).
% 32.54/32.75  thf('708', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['698', '699', '700', '703', '704', '705'])).
% 32.54/32.75  thf('709', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 32.54/32.75           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('demod', [status(thm)], ['707', '708'])).
% 32.54/32.75  thf('710', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['604', '605'])).
% 32.54/32.75  thf('711', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 32.54/32.75      inference('sup+', [status(thm)], ['709', '710'])).
% 32.54/32.75  thf('712', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['604', '605'])).
% 32.54/32.75  thf('713', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['711', '712'])).
% 32.54/32.75  thf('714', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k6_relat_1 @ X0) @ (k2_relat_1 @ sk_B))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['694', '713'])).
% 32.54/32.75  thf('715', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))
% 32.54/32.75           = (k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 32.54/32.75              (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['610', '714'])).
% 32.54/32.75  thf('716', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k3_xboole_0 @ (k9_relat_1 @ sk_B @ X0) @ (k2_relat_1 @ sk_B))
% 32.54/32.75            = (k9_relat_1 @ (k6_relat_1 @ (k9_relat_1 @ sk_B @ X0)) @ 
% 32.54/32.75               (k9_relat_1 @ sk_B @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B)
% 32.54/32.75          | ~ (v1_funct_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['138', '715'])).
% 32.54/32.75  thf('717', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['358', '368', '401', '498', '575', '591', '592', '599'])).
% 32.54/32.75  thf('718', plain,
% 32.54/32.75      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['690', '691'])).
% 32.54/32.75  thf('719', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('720', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('721', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0))
% 32.54/32.75           = (k9_relat_1 @ sk_B @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['716', '717', '718', '719', '720'])).
% 32.54/32.75  thf('722', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k9_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B) @ X0)
% 32.54/32.75            = (k9_relat_1 @ sk_B @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B)
% 32.54/32.75          | ~ (v1_funct_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['96', '721'])).
% 32.54/32.75  thf('723', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('724', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('725', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B) @ X0)
% 32.54/32.75           = (k9_relat_1 @ sk_B @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['722', '723', '724'])).
% 32.54/32.75  thf('726', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['20', '21', '22'])).
% 32.54/32.75  thf('727', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k7_relat_1 @ sk_B @ X0)) = (k9_relat_1 @ sk_B @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['95', '725', '726'])).
% 32.54/32.75  thf('728', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['305', '306'])).
% 32.54/32.75  thf('729', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B) @ X0)
% 32.54/32.75           = (k7_relat_1 @ sk_B @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['26', '29', '30'])).
% 32.54/32.75  thf('730', plain,
% 32.54/32.75      (![X32 : $i, X33 : $i]:
% 32.54/32.75         (~ (v1_funct_1 @ X32)
% 32.54/32.75          | ~ (v1_relat_1 @ X32)
% 32.54/32.75          | (v1_relat_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.75  thf('731', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((v1_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))
% 32.54/32.75          | ~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['729', '730'])).
% 32.54/32.75  thf('732', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['20', '21', '22'])).
% 32.54/32.75  thf('733', plain, (![X0 : $i]: (v1_funct_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['48', '49', '50'])).
% 32.54/32.75  thf('734', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_B @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['731', '732', '733'])).
% 32.54/32.75  thf('735', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B) @ X0)
% 32.54/32.75           = (k7_relat_1 @ sk_B @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['26', '29', '30'])).
% 32.54/32.75  thf('736', plain,
% 32.54/32.75      (![X32 : $i, X33 : $i]:
% 32.54/32.75         (~ (v1_funct_1 @ X32)
% 32.54/32.75          | ~ (v1_relat_1 @ X32)
% 32.54/32.75          | (v1_funct_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.75  thf('737', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((v1_funct_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B))
% 32.54/32.75          | ~ (v1_funct_1 @ (k8_relat_1 @ (k2_relat_1 @ sk_B) @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['735', '736'])).
% 32.54/32.75  thf('738', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['20', '21', '22'])).
% 32.54/32.75  thf('739', plain, (![X0 : $i]: (v1_funct_1 @ (k8_relat_1 @ X0 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['48', '49', '50'])).
% 32.54/32.75  thf('740', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_B @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['737', '738', '739'])).
% 32.54/32.75  thf('741', plain, (![X0 : $i]: (v2_funct_1 @ (k7_relat_1 @ sk_B @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 32.54/32.75  thf('742', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ sk_B @ X0) = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['92', '727', '728', '734', '740', '741'])).
% 32.54/32.75  thf('743', plain,
% 32.54/32.75      (![X45 : $i, X46 : $i]:
% 32.54/32.75         (((k9_relat_1 @ X46 @ (k10_relat_1 @ X46 @ X45))
% 32.54/32.75            = (k3_xboole_0 @ X45 @ (k9_relat_1 @ X46 @ (k1_relat_1 @ X46))))
% 32.54/32.75          | ~ (v1_funct_1 @ X46)
% 32.54/32.75          | ~ (v1_relat_1 @ X46))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_funct_1])).
% 32.54/32.75  thf(t17_xboole_1, axiom,
% 32.54/32.75    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 32.54/32.75  thf('744', plain,
% 32.54/32.75      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 32.54/32.75      inference('cnf', [status(esa)], [t17_xboole_1])).
% 32.54/32.75  thf('745', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X1)
% 32.54/32.75          | ~ (v1_funct_1 @ X1))),
% 32.54/32.75      inference('sup+', [status(thm)], ['743', '744'])).
% 32.54/32.75  thf('746', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((r1_tarski @ 
% 32.54/32.75           (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ X0)) @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['742', '745'])).
% 32.54/32.75  thf('747', plain,
% 32.54/32.75      (![X12 : $i, X13 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.75          | ~ (v1_relat_1 @ X12))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.75  thf('748', plain,
% 32.54/32.75      (![X9 : $i]:
% 32.54/32.75         (((k8_relat_1 @ (k2_relat_1 @ X9) @ X9) = (X9)) | ~ (v1_relat_1 @ X9))),
% 32.54/32.75      inference('cnf', [status(esa)], [t126_relat_1])).
% 32.54/32.75  thf('749', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ sk_B) = (k5_relat_1 @ sk_B @ (k6_relat_1 @ X0)))),
% 32.54/32.75      inference('sup-', [status(thm)], ['3', '4'])).
% 32.54/32.75  thf('750', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75            = (k10_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ X1))),
% 32.54/32.75      inference('demod', [status(thm)], ['115', '116'])).
% 32.54/32.75  thf('751', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k8_relat_1 @ X0 @ sk_B)) = (k10_relat_1 @ sk_B @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['749', '750'])).
% 32.54/32.75  thf('752', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('753', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k8_relat_1 @ X0 @ sk_B)) = (k10_relat_1 @ sk_B @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['751', '752'])).
% 32.54/32.75  thf('754', plain,
% 32.54/32.75      ((((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 32.54/32.75        | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['748', '753'])).
% 32.54/32.75  thf('755', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('756', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['754', '755'])).
% 32.54/32.75  thf('757', plain,
% 32.54/32.75      (![X39 : $i, X40 : $i, X41 : $i]:
% 32.54/32.75         (((k10_relat_1 @ X39 @ (k3_xboole_0 @ X40 @ X41))
% 32.54/32.75            = (k3_xboole_0 @ (k10_relat_1 @ X39 @ X40) @ 
% 32.54/32.75               (k10_relat_1 @ X39 @ X41)))
% 32.54/32.75          | ~ (v1_funct_1 @ X39)
% 32.54/32.75          | ~ (v1_relat_1 @ X39))),
% 32.54/32.75      inference('cnf', [status(esa)], [t137_funct_1])).
% 32.54/32.75  thf('758', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k10_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 32.54/32.75            = (k3_xboole_0 @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B)
% 32.54/32.75          | ~ (v1_funct_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['756', '757'])).
% 32.54/32.75  thf('759', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('760', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('761', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 32.54/32.75           = (k3_xboole_0 @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['758', '759', '760'])).
% 32.54/32.75  thf('762', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X0)
% 32.54/32.75          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 32.54/32.75      inference('simplify', [status(thm)], ['351'])).
% 32.54/32.75  thf('763', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k10_relat_1 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ X1)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X1)))),
% 32.54/32.75      inference('demod', [status(thm)], ['617', '618'])).
% 32.54/32.75  thf('764', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75            = (k3_xboole_0 @ X0 @ 
% 32.54/32.75               (k9_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75                (k2_relat_1 @ 
% 32.54/32.75                 (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))))
% 32.54/32.75          | ~ (v1_relat_1 @ 
% 32.54/32.75               (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['762', '763'])).
% 32.54/32.75  thf('765', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))
% 32.54/32.75           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['634', '635'])).
% 32.54/32.75  thf('766', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k2_relat_1 @ 
% 32.54/32.75              (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))))),
% 32.54/32.75      inference('demod', [status(thm)], ['308', '316'])).
% 32.54/32.75  thf('767', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['659', '665'])).
% 32.54/32.75  thf('768', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['587', '588', '589', '590'])).
% 32.54/32.75  thf('769', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['325', '326', '327'])).
% 32.54/32.75  thf('770', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['764', '765', '766', '767', '768', '769'])).
% 32.54/32.75  thf('771', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 32.54/32.75           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['761', '770'])).
% 32.54/32.75  thf('772', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['358', '368', '401', '498', '575', '591', '592', '599'])).
% 32.54/32.75  thf('773', plain,
% 32.54/32.75      (![X14 : $i, X15 : $i]:
% 32.54/32.75         (((k10_relat_1 @ X14 @ X15)
% 32.54/32.75            = (k10_relat_1 @ X14 @ (k3_xboole_0 @ (k2_relat_1 @ X14) @ X15)))
% 32.54/32.75          | ~ (v1_relat_1 @ X14))),
% 32.54/32.75      inference('cnf', [status(esa)], [t168_relat_1])).
% 32.54/32.75  thf('774', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k10_relat_1 @ sk_B @ X0)
% 32.54/32.75            = (k10_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['772', '773'])).
% 32.54/32.75  thf('775', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('776', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ sk_B @ X0)
% 32.54/32.75           = (k10_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['774', '775'])).
% 32.54/32.75  thf('777', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ sk_B @ X0)
% 32.54/32.75           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['771', '776'])).
% 32.54/32.75  thf('778', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['764', '765', '766', '767', '768', '769'])).
% 32.54/32.75  thf('779', plain,
% 32.54/32.75      (![X14 : $i, X15 : $i]:
% 32.54/32.75         (((k10_relat_1 @ X14 @ X15)
% 32.54/32.75            = (k10_relat_1 @ X14 @ (k3_xboole_0 @ (k2_relat_1 @ X14) @ X15)))
% 32.54/32.75          | ~ (v1_relat_1 @ X14))),
% 32.54/32.75      inference('cnf', [status(esa)], [t168_relat_1])).
% 32.54/32.75  thf('780', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 32.54/32.75      inference('demod', [status(thm)], ['118', '119', '125', '126', '127'])).
% 32.54/32.75  thf('781', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k3_xboole_0 @ 
% 32.54/32.75            (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ X1)
% 32.54/32.75            = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['779', '780'])).
% 32.54/32.75  thf('782', plain, (![X24 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 32.54/32.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 32.54/32.75  thf('783', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 32.54/32.75      inference('demod', [status(thm)], ['118', '119', '125', '126', '127'])).
% 32.54/32.75  thf('784', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 32.54/32.75      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 32.54/32.75  thf('785', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ X1))),
% 32.54/32.75      inference('demod', [status(thm)], ['781', '782', '783', '784'])).
% 32.54/32.75  thf('786', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 32.54/32.75      inference('demod', [status(thm)], ['583', '584'])).
% 32.54/32.75  thf('787', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 32.54/32.75           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ 
% 32.54/32.75              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['785', '786'])).
% 32.54/32.75  thf('788', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['698', '699', '700', '703', '704', '705'])).
% 32.54/32.75  thf('789', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k4_relat_1 @ 
% 32.54/32.75           (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 32.54/32.75              (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['787', '788'])).
% 32.54/32.75  thf('790', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['698', '699', '700', '703', '704', '705'])).
% 32.54/32.75  thf('791', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 32.54/32.75      inference('demod', [status(thm)], ['583', '584'])).
% 32.54/32.75  thf('792', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 32.54/32.75           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 32.54/32.75              (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 32.54/32.75      inference('demod', [status(thm)], ['789', '790', '791'])).
% 32.54/32.75  thf('793', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0))
% 32.54/32.75           = (k8_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0) @ 
% 32.54/32.75              (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['778', '792'])).
% 32.54/32.75  thf('794', plain,
% 32.54/32.75      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['101', '102'])).
% 32.54/32.75  thf('795', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0))
% 32.54/32.75           = (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['793', '794'])).
% 32.54/32.75  thf('796', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ (k1_relat_1 @ sk_B) @ 
% 32.54/32.75           (k6_relat_1 @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75           = (k6_relat_1 @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['777', '795'])).
% 32.54/32.75  thf('797', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0))
% 32.54/32.75           = (k6_relat_1 @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['793', '794'])).
% 32.54/32.75  thf('798', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ sk_B @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 32.54/32.75      inference('sup-', [status(thm)], ['27', '28'])).
% 32.54/32.75  thf('799', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k5_relat_1 @ 
% 32.54/32.75              (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['797', '798'])).
% 32.54/32.75  thf('800', plain,
% 32.54/32.75      (![X48 : $i, X49 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X48)
% 32.54/32.75          | (v2_funct_1 @ (k7_relat_1 @ X48 @ X49))
% 32.54/32.75          | ~ (v1_funct_1 @ X48)
% 32.54/32.75          | ~ (v1_relat_1 @ X48))),
% 32.54/32.75      inference('cnf', [status(esa)], [t84_funct_1])).
% 32.54/32.75  thf('801', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((v2_funct_1 @ 
% 32.54/32.75           (k5_relat_1 @ 
% 32.54/32.75            (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B)
% 32.54/32.75          | ~ (v1_funct_1 @ sk_B)
% 32.54/32.75          | ~ (v2_funct_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['799', '800'])).
% 32.54/32.75  thf('802', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('803', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('804', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('805', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v2_funct_1 @ 
% 32.54/32.75          (k5_relat_1 @ 
% 32.54/32.75           (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['801', '802', '803', '804'])).
% 32.54/32.75  thf('806', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v2_funct_1 @ 
% 32.54/32.75          (k5_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_B @ X0)) @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['796', '805'])).
% 32.54/32.75  thf('807', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ sk_B @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 32.54/32.75      inference('sup-', [status(thm)], ['27', '28'])).
% 32.54/32.75  thf('808', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v2_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['806', '807'])).
% 32.54/32.75  thf('809', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.75            = (k4_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 32.54/32.75          | ~ (v2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 32.54/32.75          | ~ (v1_funct_1 @ X1)
% 32.54/32.75          | ~ (v1_relat_1 @ X1))),
% 32.54/32.75      inference('simplify', [status(thm)], ['62'])).
% 32.54/32.75  thf('810', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ sk_B)
% 32.54/32.75          | ~ (v1_funct_1 @ sk_B)
% 32.54/32.75          | ((k2_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75              = (k4_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['808', '809'])).
% 32.54/32.75  thf('811', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('812', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('813', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['73', '87', '88'])).
% 32.54/32.75  thf('814', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75           = (k8_relat_1 @ (k10_relat_1 @ sk_B @ X0) @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['810', '811', '812', '813'])).
% 32.54/32.75  thf('815', plain,
% 32.54/32.75      (![X47 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X47)
% 32.54/32.75          | ((k2_relat_1 @ X47) = (k1_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.75          | ~ (v1_funct_1 @ X47)
% 32.54/32.75          | ~ (v1_relat_1 @ X47))),
% 32.54/32.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.75  thf('816', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75            = (k1_relat_1 @ 
% 32.54/32.75               (k8_relat_1 @ (k10_relat_1 @ sk_B @ X0) @ (k4_relat_1 @ sk_B))))
% 32.54/32.75          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75          | ~ (v2_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['814', '815'])).
% 32.54/32.75  thf('817', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['305', '306'])).
% 32.54/32.75  thf('818', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ (k1_relat_1 @ sk_B) @ 
% 32.54/32.75           (k6_relat_1 @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75           = (k6_relat_1 @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['777', '795'])).
% 32.54/32.75  thf('819', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k5_relat_1 @ 
% 32.54/32.75              (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['797', '798'])).
% 32.54/32.75  thf('820', plain,
% 32.54/32.75      (![X32 : $i, X33 : $i]:
% 32.54/32.75         (~ (v1_funct_1 @ X32)
% 32.54/32.75          | ~ (v1_relat_1 @ X32)
% 32.54/32.75          | (v1_relat_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.75  thf('821', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((v1_relat_1 @ 
% 32.54/32.75           (k5_relat_1 @ 
% 32.54/32.75            (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B)
% 32.54/32.75          | ~ (v1_funct_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['819', '820'])).
% 32.54/32.75  thf('822', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('823', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('824', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_relat_1 @ 
% 32.54/32.75          (k5_relat_1 @ 
% 32.54/32.75           (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['821', '822', '823'])).
% 32.54/32.75  thf('825', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_relat_1 @ 
% 32.54/32.75          (k5_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_B @ X0)) @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['818', '824'])).
% 32.54/32.75  thf('826', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ sk_B @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 32.54/32.75      inference('sup-', [status(thm)], ['27', '28'])).
% 32.54/32.75  thf('827', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['825', '826'])).
% 32.54/32.75  thf('828', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k8_relat_1 @ (k1_relat_1 @ sk_B) @ 
% 32.54/32.75           (k6_relat_1 @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75           = (k6_relat_1 @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['777', '795'])).
% 32.54/32.75  thf('829', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k5_relat_1 @ 
% 32.54/32.75              (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['797', '798'])).
% 32.54/32.75  thf('830', plain,
% 32.54/32.75      (![X32 : $i, X33 : $i]:
% 32.54/32.75         (~ (v1_funct_1 @ X32)
% 32.54/32.75          | ~ (v1_relat_1 @ X32)
% 32.54/32.75          | (v1_funct_1 @ (k7_relat_1 @ X32 @ X33)))),
% 32.54/32.75      inference('cnf', [status(esa)], [fc8_funct_1])).
% 32.54/32.75  thf('831', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((v1_funct_1 @ 
% 32.54/32.75           (k5_relat_1 @ 
% 32.54/32.75            (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B)
% 32.54/32.75          | ~ (v1_funct_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['829', '830'])).
% 32.54/32.75  thf('832', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('833', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('834', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_funct_1 @ 
% 32.54/32.75          (k5_relat_1 @ 
% 32.54/32.75           (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['831', '832', '833'])).
% 32.54/32.75  thf('835', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_funct_1 @ 
% 32.54/32.75          (k5_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_B @ X0)) @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['828', '834'])).
% 32.54/32.75  thf('836', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ sk_B @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 32.54/32.75      inference('sup-', [status(thm)], ['27', '28'])).
% 32.54/32.75  thf('837', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['835', '836'])).
% 32.54/32.75  thf('838', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v2_funct_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['806', '807'])).
% 32.54/32.75  thf('839', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['816', '817', '827', '837', '838'])).
% 32.54/32.75  thf('840', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 32.54/32.75            = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['747', '839'])).
% 32.54/32.75  thf('841', plain,
% 32.54/32.75      (![X12 : $i, X13 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.75          | ~ (v1_relat_1 @ X12))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.75  thf('842', plain,
% 32.54/32.75      (![X48 : $i, X49 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X48)
% 32.54/32.75          | (v2_funct_1 @ (k7_relat_1 @ X48 @ X49))
% 32.54/32.75          | ~ (v1_funct_1 @ X48)
% 32.54/32.75          | ~ (v1_relat_1 @ X48))),
% 32.54/32.75      inference('cnf', [status(esa)], [t84_funct_1])).
% 32.54/32.75  thf('843', plain,
% 32.54/32.75      (![X48 : $i, X49 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X48)
% 32.54/32.75          | (v2_funct_1 @ (k7_relat_1 @ X48 @ X49))
% 32.54/32.75          | ~ (v1_funct_1 @ X48)
% 32.54/32.75          | ~ (v1_relat_1 @ X48))),
% 32.54/32.75      inference('cnf', [status(esa)], [t84_funct_1])).
% 32.54/32.75  thf('844', plain,
% 32.54/32.75      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['101', '102'])).
% 32.54/32.75  thf('845', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_relat_1 @ 
% 32.54/32.75          (k5_relat_1 @ 
% 32.54/32.75           (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['821', '822', '823'])).
% 32.54/32.75  thf('846', plain,
% 32.54/32.75      ((v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['844', '845'])).
% 32.54/32.75  thf('847', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ sk_B @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 32.54/32.75      inference('sup-', [status(thm)], ['27', '28'])).
% 32.54/32.75  thf('848', plain, ((v1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['846', '847'])).
% 32.54/32.75  thf('849', plain,
% 32.54/32.75      (![X30 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X30)
% 32.54/32.75          | ((k2_funct_1 @ X30) = (k4_relat_1 @ X30))
% 32.54/32.75          | ~ (v1_funct_1 @ X30)
% 32.54/32.75          | ~ (v1_relat_1 @ X30))),
% 32.54/32.75      inference('cnf', [status(esa)], [d9_funct_1])).
% 32.54/32.75  thf('850', plain,
% 32.54/32.75      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75        | ((k2_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75            = (k4_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))
% 32.54/32.75        | ~ (v2_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup-', [status(thm)], ['848', '849'])).
% 32.54/32.75  thf('851', plain,
% 32.54/32.75      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['101', '102'])).
% 32.54/32.75  thf('852', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (v1_funct_1 @ 
% 32.54/32.75          (k5_relat_1 @ 
% 32.54/32.75           (k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k6_relat_1 @ X0)) @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['831', '832', '833'])).
% 32.54/32.75  thf('853', plain,
% 32.54/32.75      ((v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['851', '852'])).
% 32.54/32.75  thf('854', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k7_relat_1 @ sk_B @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 32.54/32.75      inference('sup-', [status(thm)], ['27', '28'])).
% 32.54/32.75  thf('855', plain, ((v1_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['853', '854'])).
% 32.54/32.75  thf('856', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k7_relat_1 @ sk_B @ X0))
% 32.54/32.75           = (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['73', '87', '88'])).
% 32.54/32.75  thf('857', plain,
% 32.54/32.75      (((k8_relat_1 @ (k1_relat_1 @ sk_B) @ (k4_relat_1 @ sk_B))
% 32.54/32.75         = (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['549', '550'])).
% 32.54/32.75  thf('858', plain,
% 32.54/32.75      ((((k2_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75          = (k4_relat_1 @ sk_B))
% 32.54/32.75        | ~ (v2_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['850', '855', '856', '857'])).
% 32.54/32.75  thf('859', plain,
% 32.54/32.75      ((~ (v1_relat_1 @ sk_B)
% 32.54/32.75        | ~ (v1_funct_1 @ sk_B)
% 32.54/32.75        | ~ (v2_funct_1 @ sk_B)
% 32.54/32.75        | ((k2_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75            = (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup-', [status(thm)], ['843', '858'])).
% 32.54/32.75  thf('860', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('861', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('862', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('863', plain,
% 32.54/32.75      (((k2_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75         = (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['859', '860', '861', '862'])).
% 32.54/32.75  thf('864', plain,
% 32.54/32.75      (![X47 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X47)
% 32.54/32.75          | ((k2_relat_1 @ X47) = (k1_relat_1 @ (k2_funct_1 @ X47)))
% 32.54/32.75          | ~ (v1_funct_1 @ X47)
% 32.54/32.75          | ~ (v1_relat_1 @ X47))),
% 32.54/32.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.54/32.75  thf('865', plain,
% 32.54/32.75      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75          = (k1_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75        | ~ (v2_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['863', '864'])).
% 32.54/32.75  thf('866', plain,
% 32.54/32.75      (((k2_relat_1 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['392', '393', '394', '395'])).
% 32.54/32.75  thf('867', plain, ((v1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['846', '847'])).
% 32.54/32.75  thf('868', plain, ((v1_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['853', '854'])).
% 32.54/32.75  thf('869', plain,
% 32.54/32.75      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75          = (k2_relat_1 @ sk_B))
% 32.54/32.75        | ~ (v2_funct_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['865', '866', '867', '868'])).
% 32.54/32.75  thf('870', plain,
% 32.54/32.75      ((~ (v1_relat_1 @ sk_B)
% 32.54/32.75        | ~ (v1_funct_1 @ sk_B)
% 32.54/32.75        | ~ (v2_funct_1 @ sk_B)
% 32.54/32.75        | ((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75            = (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup-', [status(thm)], ['842', '869'])).
% 32.54/32.75  thf('871', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('872', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('873', plain, ((v2_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('874', plain,
% 32.54/32.75      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))
% 32.54/32.75         = (k2_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['870', '871', '872', '873'])).
% 32.54/32.75  thf('875', plain,
% 32.54/32.75      ((((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 32.54/32.75        | ~ (v1_relat_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['841', '874'])).
% 32.54/32.75  thf('876', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('877', plain,
% 32.54/32.75      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['875', '876'])).
% 32.54/32.75  thf('878', plain,
% 32.54/32.75      (![X45 : $i, X46 : $i]:
% 32.54/32.75         (((k9_relat_1 @ X46 @ (k10_relat_1 @ X46 @ X45))
% 32.54/32.75            = (k3_xboole_0 @ X45 @ (k9_relat_1 @ X46 @ (k1_relat_1 @ X46))))
% 32.54/32.75          | ~ (v1_funct_1 @ X46)
% 32.54/32.75          | ~ (v1_relat_1 @ X46))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_funct_1])).
% 32.54/32.75  thf('879', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 32.54/32.75            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_relat_1 @ sk_B)
% 32.54/32.75          | ~ (v1_funct_1 @ sk_B))),
% 32.54/32.75      inference('sup+', [status(thm)], ['877', '878'])).
% 32.54/32.75  thf('880', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('881', plain, ((v1_funct_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('882', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ X0))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['879', '880', '881'])).
% 32.54/32.75  thf('883', plain, ((v1_relat_1 @ sk_B)),
% 32.54/32.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.54/32.75  thf('884', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['840', '882', '883'])).
% 32.54/32.75  thf('885', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k10_relat_1 @ (k4_relat_1 @ sk_B) @ X0))
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['659', '665'])).
% 32.54/32.75  thf('886', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ 
% 32.54/32.75           (k3_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 32.54/32.75           = (k3_xboole_0 @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['884', '885'])).
% 32.54/32.75  thf('887', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('888', plain,
% 32.54/32.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 32.54/32.75         (((k7_relat_1 @ (k7_relat_1 @ X4 @ X5) @ X6)
% 32.54/32.75            = (k7_relat_1 @ X4 @ (k3_xboole_0 @ X5 @ X6)))
% 32.54/32.75          | ~ (v1_relat_1 @ X4))),
% 32.54/32.75      inference('cnf', [status(esa)], [t100_relat_1])).
% 32.54/32.75  thf('889', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k7_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)) @ X1)
% 32.54/32.75            = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ (k3_xboole_0 @ X0 @ X1)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['887', '888'])).
% 32.54/32.75  thf('890', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B))
% 32.54/32.75           = (k7_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['251', '254', '255'])).
% 32.54/32.75  thf('891', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('892', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k7_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)) @ X1)
% 32.54/32.75           = (k4_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['889', '890', '891'])).
% 32.54/32.75  thf('893', plain,
% 32.54/32.75      (![X12 : $i, X13 : $i]:
% 32.54/32.75         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 32.54/32.75          | ~ (v1_relat_1 @ X12))),
% 32.54/32.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 32.54/32.75  thf('894', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k2_relat_1 @ 
% 32.54/32.75            (k4_relat_1 @ (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ sk_B)))
% 32.54/32.75            = (k9_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ sk_B)) @ X0))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['892', '893'])).
% 32.54/32.75  thf('895', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['462', '463'])).
% 32.54/32.75  thf('896', plain,
% 32.54/32.75      (![X0 : $i]: (v1_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['276', '277', '278'])).
% 32.54/32.75  thf('897', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k3_xboole_0 @ X1 @ X0))
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['894', '895', '896'])).
% 32.54/32.75  thf('898', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['564', '565', '570', '571', '572', '573'])).
% 32.54/32.75  thf('899', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v1_relat_1 @ X0)
% 32.54/32.75          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 32.54/32.75      inference('simplify', [status(thm)], ['351'])).
% 32.54/32.75  thf('900', plain,
% 32.54/32.75      (![X39 : $i, X40 : $i, X41 : $i]:
% 32.54/32.75         (((k10_relat_1 @ X39 @ (k3_xboole_0 @ X40 @ X41))
% 32.54/32.75            = (k3_xboole_0 @ (k10_relat_1 @ X39 @ X40) @ 
% 32.54/32.75               (k10_relat_1 @ X39 @ X41)))
% 32.54/32.75          | ~ (v1_funct_1 @ X39)
% 32.54/32.75          | ~ (v1_relat_1 @ X39))),
% 32.54/32.75      inference('cnf', [status(esa)], [t137_funct_1])).
% 32.54/32.75  thf('901', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (((k10_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 32.54/32.75            = (k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0))),
% 32.54/32.75      inference('sup+', [status(thm)], ['899', '900'])).
% 32.54/32.75  thf('902', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         (~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ((k10_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 32.54/32.75              = (k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))))),
% 32.54/32.75      inference('simplify', [status(thm)], ['901'])).
% 32.54/32.75  thf('903', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 32.54/32.75            (k3_xboole_0 @ X0 @ 
% 32.54/32.75             (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 32.54/32.75            = (k3_xboole_0 @ (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0) @ 
% 32.54/32.75               (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('sup+', [status(thm)], ['898', '902'])).
% 32.54/32.75  thf('904', plain,
% 32.54/32.75      (((k1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75         = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['381', '382', '383', '384'])).
% 32.54/32.75  thf('905', plain,
% 32.54/32.75      (((k2_relat_1 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['392', '393', '394', '395'])).
% 32.54/32.75  thf('906', plain,
% 32.54/32.75      (((k2_relat_1 @ sk_B) = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['904', '905'])).
% 32.54/32.75  thf('907', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['564', '565', '570', '571', '572', '573'])).
% 32.54/32.75  thf('908', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k3_xboole_0 @ X1 @ X0))
% 32.54/32.75           = (k9_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)], ['894', '895', '896'])).
% 32.54/32.75  thf('909', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B) = (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B))))),
% 32.54/32.75      inference('demod', [status(thm)], ['535', '542', '543', '544', '545'])).
% 32.54/32.75  thf('910', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['764', '765', '766', '767', '768', '769'])).
% 32.54/32.75  thf('911', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (~ (v2_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_funct_1 @ X0)
% 32.54/32.75          | ~ (v1_relat_1 @ X0)
% 32.54/32.75          | ((k2_funct_1 @ X0)
% 32.54/32.75              = (k4_relat_1 @ (k8_relat_1 @ (k2_relat_1 @ X0) @ X0))))),
% 32.54/32.75      inference('simplify', [status(thm)], ['247'])).
% 32.54/32.75  thf('912', plain,
% 32.54/32.75      (![X0 : $i, X1 : $i]:
% 32.54/32.75         ((k10_relat_1 @ 
% 32.54/32.75           (k4_relat_1 @ (k8_relat_1 @ X0 @ (k4_relat_1 @ sk_B))) @ X1)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X1)))),
% 32.54/32.75      inference('demod', [status(thm)], ['617', '618'])).
% 32.54/32.75  thf('913', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (((k10_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_B)) @ X0)
% 32.54/32.75            = (k3_xboole_0 @ (k2_relat_1 @ (k4_relat_1 @ sk_B)) @ 
% 32.54/32.75               (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)))
% 32.54/32.75          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 32.54/32.75          | ~ (v2_funct_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('sup+', [status(thm)], ['911', '912'])).
% 32.54/32.75  thf('914', plain,
% 32.54/32.75      (((k2_funct_1 @ (k4_relat_1 @ sk_B)) = (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['150', '157', '158', '165', '166', '167', '168', '169', '170'])).
% 32.54/32.75  thf('915', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k10_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['564', '565', '570', '571', '572', '573'])).
% 32.54/32.75  thf('916', plain,
% 32.54/32.75      (((k1_relat_1 @ sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['538', '539', '540', '541'])).
% 32.54/32.75  thf('917', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('918', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.75  thf('919', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 32.54/32.75  thf('920', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 32.54/32.75              (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['913', '914', '915', '916', '917', '918', '919'])).
% 32.54/32.75  thf('921', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 32.54/32.75  thf('922', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 32.54/32.75  thf('923', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X0 @ sk_B)) @ 
% 32.54/32.75           (k2_relat_1 @ sk_B)) = (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['903', '906', '907', '908', '909', '910', '920', '921', '922'])).
% 32.54/32.75  thf('924', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 32.54/32.75      inference('demod', [status(thm)],
% 32.54/32.75                ['764', '765', '766', '767', '768', '769'])).
% 32.54/32.75  thf('925', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0)
% 32.54/32.75           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['886', '897', '923', '924'])).
% 32.54/32.75  thf('926', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ sk_B @ X0)
% 32.54/32.75           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0)))),
% 32.54/32.75      inference('demod', [status(thm)], ['771', '776'])).
% 32.54/32.75  thf('927', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         ((k10_relat_1 @ sk_B @ X0) = (k9_relat_1 @ (k4_relat_1 @ sk_B) @ X0))),
% 32.54/32.75      inference('sup+', [status(thm)], ['925', '926'])).
% 32.54/32.75  thf('928', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 32.54/32.75  thf('929', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 32.54/32.75      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 32.54/32.75  thf('930', plain,
% 32.54/32.75      (![X0 : $i]:
% 32.54/32.75         (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) @ X0)),
% 32.54/32.75      inference('demod', [status(thm)], ['746', '927', '928', '929'])).
% 32.54/32.75  thf('931', plain, ($false), inference('demod', [status(thm)], ['0', '930'])).
% 32.54/32.75  
% 32.54/32.75  % SZS output end Refutation
% 32.54/32.75  
% 32.60/32.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
